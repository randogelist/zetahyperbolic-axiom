import Theorem_4_1_General_Odd_Zeta_Application

/-!
# Proportional families at an arbitrary fixed odd weight

The indices `N = a * (n + 1)` and `K = b * (n + 1)` give an admissible
family whenever `k`, `m`, and `a` are positive and `a < b`. Its actual
primitive integer determinant polynomials have degree `(b - a) * (n + 1)`.
These are structural facts only; no evaluation decay estimate is assumed
or proved in this module.
-/

noncomputable section

namespace ManuscriptChain.GeneralArithmetic

/-- Parameters with fixed weight and proportional determinant indices. -/
def linearParameters (k m a b n : ℕ) : Real.Parameters :=
  ⟨k, m, a * (n + 1), b * (n + 1)⟩

@[simp] theorem linearParameters_h (k m a b n : ℕ) :
    (linearParameters k m a b n).h = (b - a) * (n + 1) := by
  simp only [linearParameters, Real.Parameters.h, Nat.sub_mul]

theorem linearParameters_admissible (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    Real.Admissible (linearParameters k m a b n) := by
  refine ⟨hk, hm, ?_, ?_⟩
  · exact Nat.mul_pos ha (Nat.succ_pos n)
  · exact Nat.mul_lt_mul_of_pos_right hab (Nat.succ_pos n)

/-- An admissible family for every index, at the arbitrary odd weight `2*k+1`. -/
def linearFamily (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) : OddWeightFamily where
  k := k
  onset := 0
  parameters := linearParameters k m a b
  k_fixed := fun _ => rfl
  admissible := fun n _ => linearParameters_admissible k m a b hk hm ha hab n

@[simp] theorem linearFamily_onset (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) :
    (linearFamily k m a b hk hm ha hab).onset = 0 := rfl

@[simp] theorem linearFamily_center (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) :
    (linearFamily k m a b hk hm ha hab).center = Real.zeta (2 * k + 1) := rfl

@[simp] theorem linearFamily_parameters (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    (linearFamily k m a b hk hm ha hab).parameters n =
      linearParameters k m a b n := rfl

@[simp] theorem linearFamily_h (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ((linearFamily k m a b hk hm ha hab).parameters n).h =
      (b - a) * (n + 1) := linearParameters_h k m a b n

@[simp] theorem linearFamily_degree (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ((linearFamily k m a b hk hm ha hab).Q n).natDegree =
      (b - a) * (n + 1) := by
  rw [OddWeightFamily.degree, linearFamily_h]

end ManuscriptChain.GeneralArithmetic

#print axioms ManuscriptChain.GeneralArithmetic.linearParameters_admissible
#print axioms ManuscriptChain.GeneralArithmetic.linearFamily_degree
