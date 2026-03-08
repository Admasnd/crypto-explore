import Mathlib

/- This theorem states that any common divisor of 
   a and b must divide their greatest common divisor (gcd).
   This is also the universal property that defines the 
   gcd.
-/
theorem gcd_divisors : ∀ a b d : ℤ,  d ∣ a  
→ d ∣ b 
→ d ∣ (Int.gcd a b) := 
  fun (a b d : ℤ) => 
  fun (h₁ : d ∣ a) (h₂ : d ∣ b) => 
  -- factor a and b in terms of d using definition of divides
  /- (a = b) ▸ (P a) performs substitution to produce (P b)
     where (P a) and (P b) are propositions
  -/
  /- pattern matching on existential quantified expression
     used to perform existential elimination
  -/
  have ⟨(p : ℤ) , (hp : a = d * p)⟩  : ∃ p : ℤ, a = d * p := Int.dvd_def d a ▸ h₁    
  have ⟨(q : ℤ), (hq : b = d * q)⟩ : ∃ q : ℤ, b = d * q := Int.dvd_def d b ▸ h₂ 
  /- Use extended euclidean algorithm to compute
     the linear coefficients of a and b that such that 
     their combination equals their gcd and rewrite the equation
     in terms of d
  -/
  have h₃ : (Int.gcd a b) = d * (p * a.gcdA b + q * a.gcdB b) :=  
    calc 
        (Int.gcd a b) =  (a * a.gcdA b + b * a.gcdB b) :=  
        Int.gcd_eq_gcd_ab a b 
        _ = (d * p) * a.gcdA b + (d * q) * a.gcdB b :=
          hq ▸ hp ▸ rfl
      /- grind used to do equational reasoning that takes 
         into account associative, commutative, and distributive 
         properties of integers to rewrite equation
      -/
        _ = d * (p * a.gcdA b + q * a.gcdB b) := by grind
  have : ∃ s : ℤ, (Int.gcd a b) = d * s := 
      -- existential introduction
      ⟨ p * a.gcdA b + q * a.gcdB b, h₃ ⟩ 
    show d ∣ (Int.gcd a b) 
    from Int.dvd_def d (Int.gcd a b) ▸ this

def egcd (a b : ℤ) : ℤ × ℤ × ℤ := 
  helper (Int.natAbs a) (Int.natAbs b)
where
  helper (a : ℕ) (b : ℕ) : ℤ × ℤ × ℤ :=
   if h₁ : a = 0 then 
    (b, 0, 1) 
   else
     let q := b / a
     let r := b % a
     let (c, x', y') := helper r a
     let x := y' - q * x'
     let y := x'
     (c, x, y)
termination_by a
decreasing_by
    have h₂ : 0 < a := zero_lt_iff.mpr h₁ 
    have : r < a := Nat.mod_lt b h₂
    assumption
