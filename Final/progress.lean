import Final.arith
import Final.inversion

theorem progress : ∀ e : Expr, val e ∨ (∃ e', e ↦ e') := by
  intro e
  induction e with
  | Num => simp [*, val.DNat]
  | Binop op e1 e2 ih1 ih2 =>
    right
    cases ih1 with
    | inl v1 =>
      cases ih2 with
      | inl v2 =>
          cases v1 with
          | DNat n1 =>
              cases v2 with
              | DNat n2 =>  exact ⟨Expr.Num (apply_binop op n1 n2), steps.DOp op n1 n2⟩
      | inr ex2 =>
          let ⟨e2', hstep2⟩ := ex2
          exact ⟨Expr.Binop op e1 e2', steps.DRight op e1 e2 e2' hstep2 v1⟩
    | inr ex1 =>
        let ⟨e1', hstep1⟩ := ex1
        exact ⟨Expr.Binop op e1' e2, steps.DLeft op e1 e1' e2 hstep1⟩
