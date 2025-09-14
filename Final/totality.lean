import Final.arith
import Final.inversion
import Final.evals

theorem totality : ∀ e : Expr, ∃ e' : Expr, val e' ∧ e ↦* e' := by
  intro e
  induction e with
  | Num n =>
    exists Expr.Num n
    . constructor
      exact (val.DNat n)
      apply evals_refl
  | Binop op e1 e2 ih1 ih2 =>
    let ⟨e1', ⟨v_e1', evals_e1⟩⟩ := ih1
    let ⟨e2', ⟨v_e2', evals_e2⟩⟩ := ih2
    let ⟨n1, he1'⟩ := val_inversion e1' v_e1'
    let ⟨n2, he2'⟩ := val_inversion e2' v_e2'
    exists Expr.Num (apply_binop op n1 n2)
    apply And.intro
    . exact val.DNat _
    . have evals_left := transitive_left op e1 e1' e2 evals_e1
      have evals_right := transitive_right op e1' e2 e2' v_e1' evals_e2
      have evals_op := evals.Step _ _ _ (steps.DOp op n1 n2) (evals_refl _)
      rw [←he1', ←he2'] at evals_op
      exact (evals_trans evals_left (evals_trans evals_right evals_op))
