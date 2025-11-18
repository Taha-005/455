from flask import Flask, render_template, request, jsonify, redirect, url_for, flash, session
from flask_sqlalchemy import SQLAlchemy
from flask_login import LoginManager, UserMixin, login_user, logout_user, current_user, login_required
from werkzeug.security import generate_password_hash, check_password_hash
import random
import math
from datetime import datetime
import os



app = Flask(__name__)
app.config["SECRET_KEY"] = os.environ.get("SECRET_KEY", "dev-secret-key-change-in-production")
app.config["SQLALCHEMY_DATABASE_URI"] = os.environ.get("DATABASE_URL", "sqlite:///mathforge.db")
app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False

# Initialize extensions
db = SQLAlchemy(app)
login_manager = LoginManager(app)
login_manager.login_view = "login"
login_manager.login_message = "Please log in to access this feature."

# ========================================
# DATABASE MODELS
# ========================================
class User(db.Model, UserMixin):
    __tablename__ = "users"
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(80), unique=True, nullable=False)
    email = db.Column(db.String(120), unique=True, nullable=True)
    password_hash = db.Column(db.String(200), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    calculations = db.relationship("Calculation", backref="user", lazy=True, cascade="all, delete-orphan")
    
    def set_password(self, password):
        self.password_hash = generate_password_hash(password)
    
    def verify_password(self, password):
        return check_password_hash(self.password_hash, password)

class Calculation(db.Model):
    __tablename__ = "calculations"
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=True)
    operation_type = db.Column(db.String(50), nullable=False)
    input_values = db.Column(db.Text, nullable=False)
    output_result = db.Column(db.Text, nullable=False)
    notes = db.Column(db.Text, nullable=True)
    is_starred = db.Column(db.Boolean, default=False)
    computed_at = db.Column(db.DateTime, default=datetime.utcnow)

@login_manager.user_loader
def load_user(user_id):
    return User.query.get(int(user_id))

# ========================================
# MATHEMATICAL FUNCTIONS
# ========================================

def decompose_into_primes(number):
    """Breaks down a number into its prime factors with exponents."""
    if number < 2:
        return {}
    
    prime_powers = {}
    
    # Handle factor of 2
    while number % 2 == 0:
        prime_powers[2] = prime_powers.get(2, 0) + 1
        number //= 2
    
    # Check odd factors
    divisor = 3
    while divisor * divisor <= number:
        while number % divisor == 0:
            prime_powers[divisor] = prime_powers.get(divisor, 0) + 1
            number //= divisor
        divisor += 2
    
    # If number > 1, then it's a prime factor
    if number > 1:
        prime_powers[number] = prime_powers.get(number, 0) + 1
    
    return prime_powers

def compute_phi_function(number):
    """Calculates Euler's totient function φ(n)."""
    if number < 1:
        return 0
    if number == 1:
        return 1
    
    prime_factors = decompose_into_primes(number)
    phi_value = number
    
    for prime in prime_factors:
        phi_value -= phi_value // prime
    
    return phi_value

def probabilistic_primality_test(number, rounds=10):
    """Miller-Rabin probabilistic primality test."""
    if number < 2:
        return False
    if number == 2 or number == 3:
        return True
    if number % 2 == 0:
        return False
    
    # Small prime check
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    for p in small_primes:
        if number == p:
            return True
        if number % p == 0:
            return False
    
    # Write n-1 as 2^r * d
    r, d = 0, number - 1
    while d % 2 == 0:
        d //= 2
        r += 1
    
    def witness_test(a, s, d, n):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            return True
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                return True
        return False
    
    for _ in range(rounds):
        witness = random.randrange(2, number - 1)
        if not witness_test(witness, r, d, number):
            return False
    
    return True

def modular_power(base, exponent, modulus=None):
    """Efficient exponentiation with optional modulus."""
    if modulus:
        return pow(base, exponent, modulus)
    return base ** exponent

def extended_euclidean(a, b):
    """Returns gcd, and coefficients x, y such that ax + by = gcd(a,b)."""
    if a == 0:
        return b, 0, 1
    
    gcd_val, x1, y1 = extended_euclidean(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    
    return gcd_val, x, y

def find_modular_inverse(a, m):
    """Finds the modular inverse of a mod m."""
    gcd_val, x, _ = extended_euclidean(a, m)
    
    if gcd_val != 1:
        return None  # Modular inverse doesn't exist
    
    return (x % m + m) % m

def solve_congruence_system(remainders, moduli):
    """Solves a system of congruences using Chinese Remainder Theorem."""
    if len(remainders) != len(moduli):
        raise ValueError("Remainders and moduli lists must have the same length")
    
    total_product = 1
    for m in moduli:
        total_product *= m
    
    solution = 0
    for remainder, modulus in zip(remainders, moduli):
        partial_product = total_product // modulus
        inverse = find_modular_inverse(partial_product, modulus)
        solution += remainder * partial_product * inverse
    
    return solution % total_product

def compute_gcd(a, b):
    """Computes the greatest common divisor using Euclidean algorithm."""
    while b:
        a, b = b, a % b
    return a

def compute_lcm(a, b):
    """Computes the least common multiple."""
    return abs(a * b) // compute_gcd(a, b)

# ========================================
# FORMATTING HELPER FUNCTIONS
# ========================================

def to_superscript(n):
    """Convert number to superscript unicode."""
    superscripts = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
    return str(n).translate(superscripts)

def format_factorization_for_display(n, factors):
    """Format factorization as: 60 = 2² × 3 × 5"""
    if not factors:
        return f"{n} = 1"
    
    parts = []
    for prime in sorted(factors.keys()):
        exp = factors[prime]
        if exp == 1:
            parts.append(str(prime))
        else:
            parts.append(f"{prime}{to_superscript(exp)}")
    
    return f"{n} = {' × '.join(parts)}"

def format_modular_exp_for_display(base, exp, mod, result):
    """Format modular exponentiation as: 3¹⁰⁰ ≡ 4 (mod 7)"""
    return f"{base}{to_superscript(exp)} ≡ {result} (mod {mod})"

def format_crt_for_display(remainders, moduli, solution):
    """Format CRT solution as: x ≡ 11 (mod 60)"""
    product = math.prod(moduli)
    return f"x ≡ {solution} (mod {product})"

def format_gcd_lcm_for_display(a, b, gcd_val, lcm_val):
    """Format GCD/LCM as: GCD(48, 18) = 6, LCM(48, 18) = 144"""
    return f"GCD({a}, {b}) = {gcd_val}, LCM({a}, {b}) = {lcm_val}"

def format_primality_for_display(n, is_prime):
    """Format primality result as: 7 is PRIME or 33 is COMPOSITE"""
    return f"{n} is {'PRIME' if is_prime else 'COMPOSITE'}"

def format_euler_phi_for_display(n, phi):
    """Format Euler's totient as: φ(100) = 40"""
    return f"φ({n}) = {phi}"

# ========================================
# HELPER FUNCTIONS
# ========================================

def record_calculation(operation, inputs, result):
    """Records a calculation to database or session."""
    if current_user.is_authenticated:
        calc = Calculation(
            user_id=current_user.id,
            operation_type=operation,
            input_values=str(inputs),
            output_result=result
        )
        db.session.add(calc)
        db.session.commit()
    else:
        # Store in session for anonymous users
        session_key = f"calc_{operation}"
        history = session.get(session_key, [])
        history.append({
            "inputs": str(inputs),
            "result": result,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        session[session_key] = history[-15:]  # Keep last 15

def fetch_calculation_history(operation):
    """Retrieves calculation history with formatted display."""
    if current_user.is_authenticated:
        calcs = Calculation.query.filter_by(
            user_id=current_user.id,
            operation_type=operation
        ).order_by(Calculation.computed_at.desc()).limit(15).all()
        
        return [{
            "id": c.id,
            "inputs": format_inputs_for_display(operation, c.input_values),
            "result": c.output_result,
            "timestamp": c.computed_at.strftime("%Y-%m-%d %H:%M:%S"),
            "starred": c.is_starred
        } for c in calcs]
    else:
        session_key = f"calc_{operation}"
        history = session.get(session_key, [])
        
        # Format inputs for display
        formatted_history = []
        for item in history:
            formatted_item = item.copy()
            formatted_item["inputs"] = format_inputs_for_display(operation, item["inputs"])
            formatted_history.append(formatted_item)
        
        return formatted_history

def format_inputs_for_display(operation, inputs_str):
    """Format input string into readable format."""
    try:
        # Parse the input string safely
        inputs_dict = eval(inputs_str)
        
        if operation == "factorization":
            return f"{inputs_dict.get('n', 'N/A')}"
        
        elif operation == "euler_phi":
            return f"{inputs_dict.get('n', 'N/A')}"
        
        elif operation == "primality":
            n = inputs_dict.get('n', 'N/A')
            return f"{n}"
        
        elif operation == "mod_exp":
            base = inputs_dict.get('base', 'N/A')
            exp = inputs_dict.get('exp', 'N/A')
            mod = inputs_dict.get('mod', 'N/A')
            return f"{base}{to_superscript(exp)} mod {mod}"
        
        elif operation == "crt":
            if 'remainders' in inputs_dict:
                remainders = inputs_dict.get('remainders', [])
                moduli = inputs_dict.get('moduli', [])
                # Format as system of congruences
                parts = [f"x ≡ {r} (mod {m})" for r, m in zip(remainders, moduli)]
                return ", ".join(parts)
            else:
                number = inputs_dict.get('number', 'N/A')
                moduli = inputs_dict.get('moduli', [])
                return f"{number} mod {moduli}"
        
        elif operation == "gcd_lcm":
            a = inputs_dict.get('a', 'N/A')
            b = inputs_dict.get('b', 'N/A')
            return f"{a}, {b}"
        
        elif operation == "mod_inverse":
            a = inputs_dict.get('a', 'N/A')
            m = inputs_dict.get('m', 'N/A')
            return f"{a} mod {m}"
        
        else:
            return inputs_str
            
    except:
        # If parsing fails, return original string
        return inputs_str

# ========================================
# ROUTES
# ========================================

@app.route("/")
@login_required
def index():
    return render_template("index.html")

@app.route("/register", methods=["GET", "POST"])
def register():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        email = request.form.get("email", "").strip()
        password = request.form.get("password", "")
        
        if not username or not password:
            flash("Username and password are required.", "error")
            return redirect(url_for("register"))
        
        if User.query.filter_by(username=username).first():
            flash("Username already taken. Please choose another.", "error")
            return redirect(url_for("register"))
        
        new_user = User(username=username, email=email if email else None)
        new_user.set_password(password)
        db.session.add(new_user)
        db.session.commit()
        
        login_user(new_user)
        flash("Registration successful! Welcome to MathForge.", "success")
        return redirect(url_for("index"))
    
    return render_template("register.html")

@app.route("/login", methods=["GET", "POST"])
def login():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "").strip()
        
        user = User.query.filter_by(username=username).first()
        
        if user and user.verify_password(password):
            login_user(user)
            flash(f"Welcome back, {username}!", "success")
            next_page = request.args.get("next")
            return redirect(next_page if next_page else url_for("index"))
        else:
            flash("Invalid username or password.", "error")
    
    return render_template("login.html")

@app.route("/logout")
@login_required
def logout():
    logout_user()
    flash("You've been logged out successfully.", "info")
    return redirect(url_for("login"))

@app.route("/factorization")
def factorization():
    history = fetch_calculation_history("factorization")
    return render_template("factorization.html", history=history)

@app.route("/euler-phi")
def euler_phi():
    history = fetch_calculation_history("euler_phi")
    return render_template("euler_phi.html", history=history)

@app.route("/primality-test")
def primality_test():
    history = fetch_calculation_history("primality")
    return render_template("primality.html", history=history)

@app.route("/modular-exponentiation")
def modular_exponentiation():
    history = fetch_calculation_history("mod_exp")
    return render_template("modular_exp.html", history=history)

@app.route("/chinese-remainder")
def chinese_remainder():
    history = fetch_calculation_history("crt")
    return render_template("crt.html", history=history)

@app.route("/gcd-lcm")
def gcd_lcm():
    history = fetch_calculation_history("gcd_lcm")
    return render_template("gcd_lcm.html", history=history)

@app.route("/modular-inverse")
def modular_inverse():
    history = fetch_calculation_history("mod_inverse")
    return render_template("mod_inverse.html", history=history)

@app.route("/calculate", methods=["POST"])
def calculate():
    """Unified calculation endpoint."""
    data = request.get_json()
    operation = data.get("operation")
    result_text = ""
    
    try:
        if operation == "factorization":
            n = int(data["number"])
            factors = decompose_into_primes(n)
            result_text = format_factorization_for_display(n, factors)
            record_calculation("factorization", {"n": n}, result_text)
            
        elif operation == "euler_phi":
            n = int(data["number"])
            phi = compute_phi_function(n)
            result_text = format_euler_phi_for_display(n, phi)
            record_calculation("euler_phi", {"n": n}, result_text)
            
        elif operation == "primality":
            n = int(data["number"])
            rounds = int(data.get("rounds", 10))
            is_prime = probabilistic_primality_test(n, rounds)
            result_text = format_primality_for_display(n, is_prime)
            record_calculation("primality", {"n": n, "rounds": rounds}, result_text)
            
        elif operation == "mod_exp":
            base = int(data["base"])
            exp = int(data["exponent"])
            mod = int(data["modulus"])
            
            result = modular_power(base, exp, mod)
            result_text = format_modular_exp_for_display(base, exp, mod, result)
            record_calculation("mod_exp", {"base": base, "exp": exp, "mod": mod}, result_text)
            
        elif operation == "crt":
            remainders = list(map(int, data["remainders"].split(",")))
            moduli = list(map(int, data["moduli"].split(",")))
            solution = solve_congruence_system(remainders, moduli)
            result_text = format_crt_for_display(remainders, moduli, solution)
            record_calculation("crt", {"remainders": remainders, "moduli": moduli}, result_text)
                
        elif operation == "gcd_lcm":
            a = int(data["a"])
            b = int(data["b"])
            gcd = compute_gcd(a, b)
            lcm = compute_lcm(a, b)
            result_text = format_gcd_lcm_for_display(a, b, gcd, lcm)
            record_calculation("gcd_lcm", {"a": a, "b": b}, result_text)
            
        elif operation == "mod_inverse":
            a = int(data["a"])
            m = int(data["m"])
            inverse = find_modular_inverse(a, m)
            
            if inverse is not None:
                result_text = f"Modular inverse of {a} mod {m} = {inverse}"
            else:
                result_text = f"Modular inverse does not exist (gcd({a}, {m}) ≠ 1)"
            
            record_calculation("mod_inverse", {"a": a, "m": m}, result_text)
            
        return jsonify({"success": True, "result": result_text})
        
    except Exception as e:
        return jsonify({"success": False, "result": f"Error: {str(e)}"})

@app.route("/clear-history/<operation>", methods=["POST"])
@login_required
def clear_history(operation):
    """Clear calculation history for a specific operation."""
    try:
        Calculation.query.filter_by(
            user_id=current_user.id,
            operation_type=operation
        ).delete()
        db.session.commit()
        return jsonify({"success": True})
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})

@app.route("/profile")
@login_required
def profile():
    recent_calcs = Calculation.query.filter_by(
        user_id=current_user.id
    ).order_by(Calculation.computed_at.desc()).limit(20).all()
    
    # Format the calculations for display
    formatted_calcs = []
    for calc in recent_calcs:
        formatted_calc = {
            'id': calc.id,
            'operation_type': calc.operation_type,
            'input_values': format_inputs_for_display(calc.operation_type, calc.input_values),
            'output_result': calc.output_result,
            'computed_at': calc.computed_at
        }
        formatted_calcs.append(formatted_calc)
    
    return render_template("profile.html", calculations=formatted_calcs)

# ========================================
# MAIN
# ========================================
if __name__ == "__main__":
    with app.app_context():
        db.create_all()
    app.run(debug=False, port=5000, use_reloader=False)