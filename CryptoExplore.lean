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


def egcd (a b : ℤ) : ℕ × ℤ × ℤ := 
  egcd_helper (Int.natAbs a) (Int.natAbs b)
  where egcd_helper (a : ℕ) (b : ℕ) : ℕ × ℤ × ℤ :=
    if h₁ : a = 0 then 
      (b, 0, 1) 
    else
      let (c, x', y') := egcd_helper (b % a) a
      (c, (y' - (b / a) * x'), x')
  termination_by a
  decreasing_by
  {
    have h₂ : 0 < a := zero_lt_iff.mpr h₁ 
    have : (b % a) < a := Nat.mod_lt b h₂
    assumption
  }


theorem egcd_divides (a b : ℕ) : 
    (egcd a b).1 ∣ a ∧ (egcd a b).1 ∣ b := by
  unfold egcd 
  fun_induction egcd.egcd_helper a b with
    | case1 b => 
      simp only
      show b ∣ 0 ∧ b ∣ b 
      /- leverage fact that every number divides zero and 
         every number divides itself.
      -/
      exact ⟨ Nat.dvd_zero b, Nat.dvd_refl b⟩ 
    | case2 a b h₁ c x' y' h₂ h_ind =>
      simp only
      show c ∣ a ∧ c ∣ b 
      have : (egcd.egcd_helper (b % a) a).1 = c := by grind only
      have h₃ : c ∣ a := by grind only
      have h₄ : c ∣ (b % a) := by grind only
      have h₅ : c ∣ b := (Nat.dvd_mod_iff h₃).mp h₄
      exact ⟨ h₃,h₅ ⟩ 

theorem egcd_gcd (a b d : ℕ) (h₁ : d ∣ a) (h₂ : d ∣ b)
  : d ∣ (egcd a b).1 := by
    unfold egcd
    fun_induction egcd.egcd_helper a b with
      | case1 b => 
        simp only
        show d ∣ b
        assumption
      | case2 a b h c x' y' h₃ h_ind =>
        simp only
        show d ∣ c
        have h_ind' : d ∣ (b % a) → d ∣ a → d ∣ c := by grind only
        have h₃ : d ∣ (b % a) := (Nat.dvd_mod_iff h₁).mpr h₂ 
        exact h_ind' h₃ h₁
        
theorem egcd_equation  (a b d: ℕ) 
  : a * (egcd a b).2.1 + b * (egcd a b).2.2 = 
  (egcd a b).1 := sorry
