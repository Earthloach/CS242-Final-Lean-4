import Final.arith

@[simp]
theorem val_inversion : ∀ e : Expr, val e → ∃ n : Nat, e = Expr.Num n := by
  intro _ hva
  cases hva
  simp

-- Term proof
-- theorem val_inversion : ∀ e : Expr, val e → ∃ n : Nat, e = Expr.Num n :=
--   fun e he =>
--     match he with
--     | Dnat n => ⟨n, rfl⟩
