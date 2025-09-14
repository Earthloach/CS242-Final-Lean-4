inductive Binop | Add | Sub | Mul | Div
example : Binop := Binop.Add


inductive Expr
| Num : Nat → Expr
| Binop : Binop → Expr → Expr → Expr
| Var : Nat → Expr
| Let : Expr → Expr → Expr
-- Fill in Let and Var syntax

example : Expr := Expr.Num 1
example : Expr := Expr.Binop Binop.Add (Expr.Num 1) (Expr.Num 2)


inductive val : Expr → Prop
| DNat (n : Nat) : val (Expr.Num n)

example : val (Expr.Num 2) := val.DNat 2


def apply_binop (op : Binop) (nl nr : Nat) : Nat :=
  Binop.casesOn op (nl + nr) (nl - nr) (nl * nr) (nl / nr)

inductive subst : Nat → Expr → Expr → Expr → Prop
| SNum (i n : Nat) (e' : Expr) : subst i e' (Expr.Num n) (Expr.Num n)
| SBinop (op : Binop) (i : Nat) (el er el' er' e' : Expr) :
  subst i e' el el' → subst i e' er er' →
  subst i e' (Expr.Binop op el er) (Expr.Binop op el' er')
| SLet (i : Nat) (evar evar' ebody ebody' e' : Expr) :
  subst i e' evar evar' → subst (i + 1) e' ebody ebody' →
  subst i e' (Expr.Let evar ebody) (Expr.Let evar' ebody')
| SVar (i j : Nat) (e' : Expr) : j < i → subst i e' (Expr.Var j) (Expr.Var j)
| SVarEq (i : Nat) (e' : Expr) : subst i e' (Expr.Var i) e'
-- Fill in remaining substitution rules

inductive steps : Expr → Expr → Prop
| DLeft (op : Binop) (el el' er : Expr) :
  steps el el' →
  steps
    (Expr.Binop op el er)
    (Expr.Binop op el' er)
| DRight (op : Binop) (el er er' : Expr) :
  steps er er' → val el →
  steps
    (Expr.Binop op el er)
    (Expr.Binop op el er')
| DOp (op: Binop) (nl nr : Nat) :
  steps
    (Expr.Binop op (Expr.Num nl) (Expr.Num nr))
    (Expr.Num (apply_binop op nl nr))
| DLet (evar ebody ebody' : Expr) :
  subst 0 evar ebody ebody' →
  steps
  (Expr.Let evar ebody)
  (ebody')

-- Fill in D-Let step rule

notation:35 e " ↦ " e' => steps e e'

example : (Expr.Binop Binop.Add (Expr.Num 1) (Expr.Num 2)) ↦ (Expr.Num 3) :=
   steps.DOp Binop.Add 1 2

inductive valid : Nat → Expr → Prop
| TNum (n i : Nat) :
  valid i (Expr.Num n)
| TBinop (op : Binop) (el er : Expr) (i : Nat) :
  valid i el → valid i er → valid i (Expr.Binop op el er)
| TLet (evar ebody : Expr) (i : Nat) :
  valid i evar → valid (i + 1) ebody → valid i (Expr.Let evar ebody)
| TVar (i j : Nat) :
  j < i → valid i (Expr.Var j)
-- Fill in T-Let and T-Var rules

theorem valid_inner_ctx {e : Expr} {i : Nat} :
    valid i e → valid (i + 1) e := by
    intro hv
    induction hv
    case TNum => apply valid.TNum
    case TBinop ihl ihr => apply valid.TBinop _ _ _ _ ihl ihr
    case TLet ihvar ihbody => apply valid.TLet _ _ _ ihvar ihbody
    case TVar i _ hlt =>
      apply valid.TVar
      have hlt_plus_one : i < i + 1 := by simp
      apply Nat.lt_trans hlt hlt_plus_one


theorem subst_preserves_valid :
  ∀ (e e' esub : Expr), ∀ (i : Nat),
    valid (i + 1) e → valid i e' → subst i e' e esub → valid i esub := by
    intro _ _ _ _ hvbody hvvar hsub
    induction hsub
    . case SNum => apply valid.TNum
    . case SBinop hl hr ihl ihr =>
     apply valid.TBinop
     . match hvbody with
       | valid.TBinop _ _ _ _ hvl' _ => exact ihl hvl' hvvar
     . match hvbody with
       | valid.TBinop _ _ _ _ _ hvr' => exact ihr hvr' hvvar
    . case SLet i evar _ _ _ _ hvar hbody ihvar ihbody =>
      apply valid.TLet
      . match hvbody with
        | valid.TLet _ _ _ hvvar' _ => exact ihvar hvvar' hvvar
      . match hvbody with
        | valid.TLet _ _ _ _ hvbody' => exact ihbody hvbody' (valid_inner_ctx hvvar)
    . case SVar => apply valid.TVar; assumption
    . case SVarEq => assumption

theorem preservation :
  ∀ e e' : Expr, (e ↦ e') → valid 0 e → valid 0 e' := by
  intro e e' hstep hve
  induction e
  . case Num => contradiction
  . case Binop op el er ihl ihr =>
    cases hstep
    . case DLeft el' hl =>
      apply valid.TBinop
      apply preservation el el' hl
      cases hve; assumption
      cases hve; assumption
    . case DRight er' _ hr =>
      apply valid.TBinop
      cases hve; assumption
      apply preservation er er' hr
      cases hve; assumption
    . case DOp => apply valid.TNum
  . case Var => contradiction
  . case Let evar ebody ihvar ihbody =>
    cases hstep
    . case DLet hsub =>
      apply subst_preserves_valid _ _ _ _ _ _ hsub <;> cases hve <;> assumption

