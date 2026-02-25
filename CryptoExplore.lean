import Mathlib

/- This theorem states that any common divisor of 
   a and b must divide their greatest common divisor
-/
theorem gcd_divisors : ∀ a b d : ℤ,  d ∣ a  
→ d ∣ b 
→ d ∣ (Int.gcd a b) := 
  fun (a b d : ℤ) => 
  fun (h₁ : d ∣ a) (h₂ : d ∣ b) => 
  -- factor a in terms of d using definition of divides
  have h₃ : ∃ p : ℤ, a = d * p := Int.dvd_def d a ▸ h₁    
  -- factor b in terms of d using definition of divides
  have h₄ : ∃ q : ℤ, b = d * q := Int.dvd_def d b ▸ h₂ 
  /- Use extended euclidean algorithm to compute compute
     the linear coefficients of a and b that such that 
     their combination equals their gcd
  -/
  have h₅ : (Int.gcd a b) = a * a.gcdA b + b * a.gcdB b := 
    Int.gcd_eq_gcd_ab a b 
  -- Consider the factors of d that equal a and b 
  -- Using match statement to do existential elimination
  match h₃, h₄ with
    | ⟨ (p : ℤ), (hp : a = d * p) ⟩, ⟨(q : ℤ), (hq : b = d * q)⟩ => 
    -- rewrite above linear equation to relate d to gcd(a,b) 
    have : (Int.gcd a b) = (d * p) * a.gcdA b + (d * q) * a.gcdB b :=
    hq ▸ (hp ▸ h₅ ) 
    -- rewrite linear equation to make clear that d | gcd(a,b)
    /- grind used to do equational reasoning that takes 
       into account associativity and commutativity necessary
       to rewrite equation
    -/
    have : (Int.gcd a b) = (p * a.gcdA b + q * a.gcdB b) * d := 
    by grind
    have : ∃ s : ℤ, (Int.gcd a b) = d * s := 
      -- existential introduction
      ⟨ p * a.gcdA b + q * a.gcdB b, by grind⟩ 
    /- Reworked linear equation proves any common divisor d 
       of a and b divides their gcd based on the definition of divides
    -/
    show d ∣ (Int.gcd a b) 
    from Int.dvd_def d (Int.gcd a b) ▸ this
