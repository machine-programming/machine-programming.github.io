open Complex

theorem conj_mul_self (z : ℂ) :
  z * conj z = ⟨z.re^2 + z.im^2, 0⟩ := by
  simp [mul_conj, re, im]
