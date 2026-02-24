import Mathlib


-- ε–δ definition

/-- `LimitEpsDel f a L` means that the function `f : ℝ → ℝ` has limit `L`
at the point `a` in the ε–δ sense. -/
def LimitEpsDel (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε


-- interval definition

/-- `OpenInterval a b` is the open interval `(a, b) ⊆ ℝ`. -/
def OpenInterval (a b : ℝ) : Set ℝ := { x : ℝ | a < x ∧ x < b }

/-- `OpenIntervalContaining I L` means that `I` is an open interval
containing the point `L`. -/
def OpenIntervalContaining (I : Set ℝ) (L : ℝ) : Prop :=
  ∃ u v : ℝ, u < L ∧ L < v ∧ I = OpenInterval u v

/-- `LimitSeq f a L` means that the function `f : ℝ → ℝ` has limit `L`
at the point `a` in the interval sense. -/
def LimitInterval (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ I : Set ℝ, OpenIntervalContaining I L →
    ∃ J : Set ℝ, OpenIntervalContaining J a ∧
      ∀ x : ℝ, (x ∈ J ∧ x ≠ a) → f x ∈ I


-- sequential definition

/-- `TendsTo a t` means that the real sequence `a : ℕ → ℝ`
converges to the real number `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-- `LimitSeq f a L` means that the function `f : ℝ → ℝ` has limit `L`
at the point `a` in the sequential sense. -/
def LimitSeq (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ x : ℕ → ℝ, (∀ n, x n ≠ a) →
    TendsTo x a → TendsTo (fun n => f (x n)) L


-- ε–δ → interval

/-- `LimitEpsDel_imp_LimitInterval f a L` states that the ε–δ definition
of the limit implies the interval definition. -/
theorem LimitEpsDel_imp_LimitInterval (f : ℝ → ℝ) (a L : ℝ) :
  LimitEpsDel f a L → LimitInterval f a L := by
  intro hεδ I hI
  rcases hI with ⟨u, v, huL, hLv, rfl⟩

  -- define ε so that (L-ε, L+ε) ⊆ (u,v)
  let ε : ℝ := min (L - u) (v - L)
  have hεpos : ε > 0 := by
    have h1 : L - u > 0 := sub_pos.2 huL
    have h2 : v - L > 0 := sub_pos.2 hLv
    exact lt_min h1 h2

  rcases hεδ ε hεpos with ⟨δ, hδpos, hδ⟩

  -- define J = (a-δ, a+δ) that contains a
  refine ⟨OpenInterval (a - δ) (a + δ), ?_, ?_⟩
  refine ⟨a - δ, a + δ, ?_, ?_, rfl⟩ <;> linarith

  -- show ∀ x, (x ∈ J ∧ x ≠ a) → f x ∈ (u,v)
  intro x hx
  have hxJ : x ∈ OpenInterval (a - δ) (a + δ) := hx.1
  have hxa : x ≠ a := hx.2
  rcases hxJ with ⟨hx1, hx2⟩

  -- derive |x - a| < δ
  have hxabs : |x - a| < δ := by
    have hleft : -δ < x - a := by linarith
    have hright : x - a < δ := by linarith
    exact (abs_lt).2 ⟨hleft, hright⟩

  -- derive 0 < |x - a|
  have hxpos : 0 < |x - a| := by
    exact abs_pos.2 (sub_ne_zero.2 hxa)

  -- apply ε–δ hypothesis to get |f x - L| < ε
  have hfx : |f x - L| < ε := hδ x ⟨hxpos, hxabs⟩

  -- turn |f x - L| < ε into L-ε < f x < L+ε
  have hband : L - ε < f x ∧ f x < L + ε := by
    have hfx' : -ε < f x - L ∧ f x - L < ε := (abs_lt).1 hfx
    constructor <;> linarith

  -- bounds from ε
  have hε1 : ε ≤ L - u := min_le_left _ _
  have hε2 : ε ≤ v - L := min_le_right _ _

  -- conclude u < f x and f x < v i.e. f x ∈ (u,v)
  refine ⟨?_, ?_⟩ <;> linarith


-- interval → sequential

/-- `LimitInterval_imp_LimitSeq f a L` states that the interval definition
of the limit implies the sequential definition. -/
theorem LimitInterval_imp_LimitSeq (f : ℝ → ℝ) (a L : ℝ) :
  LimitInterval f a L → LimitSeq f a L := by
  intro hInt x hxne hxto ε hεpos

  -- define I = (L-ε, L+ε)
  let I : Set ℝ := OpenInterval (L - ε) (L + ε)
  have hIcont : OpenIntervalContaining I L := by
    refine ⟨L - ε, L + ε, ?_, ?_, rfl⟩ <;> linarith

  -- define J = (p,q) that contains a
  rcases hInt I hIcont with ⟨J, hJcont, hJmap⟩
  rcases hJcont with ⟨p, q, hp, hq, rfl⟩

  -- define η = min (a-p) (q-a)
  let η : ℝ := min (a - p) (q - a)
  have hηpos : η > 0 := by
    have h1 : a - p > 0 := sub_pos.2 hp
    have h2 : q - a > 0 := sub_pos.2 hq
    exact lt_min h1 h2

  rcases hxto η hηpos with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n hn

  -- turn |x n - a| < η into a-η < x n < a+η
  have hxabs : |x n - a| < η := hB n hn
  have hxband : a - η < x n ∧ x n < a + η := by
    have hxband' : -η < x n - a ∧ x n - a < η := (abs_lt).1 hxabs
    constructor <;> linarith

  -- bounds from η
  have hη1 : η ≤ a - p := min_le_left _ _
  have hη2 : η ≤ q - a := min_le_right _ _

  -- show p < x n and x n < q
  have hxJ : x n ∈ OpenInterval p q := by
    refine ⟨?_, ?_⟩ <;> linarith

  -- show f: f(x n) ∈ I
  have hfxI : f (x n) ∈ I := by
    apply hJmap
    exact ⟨hxJ, hxne n⟩

  -- conclude |f(x n) - L| < ε
  rcases hfxI with ⟨hfx1, hfx2⟩
  have hfx : |f (x n) - L| < ε := by
    apply (abs_lt).2
    constructor <;> linarith
  simpa using hfx


-- sequential → ε–δ

/-- `LimitSeq_imp_LimitEpsDel f a L` states that the sequential definition
of the limit implies the ε–δ definition. -/
theorem LimitSeq_imp_LimitEpsDel (f : ℝ → ℝ) (a L : ℝ) :
  LimitSeq f a L → LimitEpsDel f a L := by
  intro hSeq

  -- prove ε–δ by contradiction
  by_contra hNot
  unfold LimitEpsDel at hNot
  push_neg at hNot
  rcases hNot with ⟨η, hηpos, hbad⟩

  -- choose x n for δ = 1/(n+1)
  have hδpos : ∀ n : ℕ, (0 : ℝ) < (1 / (n + 1 : ℝ)) := by
    intro n
    have hδpos' : (0 : ℝ) < (n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos n)
    exact one_div_pos.2 hδpos'
  choose x hx using (fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (hδpos n))

  -- show x n ≠ a
  have hxane : ∀ n : ℕ, x n ≠ a := by
    intro n
    have hxapos : 0 < |x n - a| := (hx n).1.1
    have hxane' : x n - a ≠ 0 := by exact abs_pos.mp hxapos
    exact sub_ne_zero.mp hxane'

  -- show x n tends to a
  have hxto : TendsTo x a := by
    intro ε hεpos
    obtain ⟨B, hBε⟩ : ∃ B : ℕ, (1 / (B + 1 : ℝ)) < ε := by
      simpa using exists_nat_one_div_lt hεpos
    refine ⟨B, ?_⟩
    intro n hn
    have hxlt : |x n - a| < 1 / (n + 1 : ℝ) := (hx n).1.2
    have hBn : (B + 1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hn
    have hBpos : (0 : ℝ) < (B + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos B)
    have h1n : (1 / (n + 1 : ℝ)) ≤ (1 / (B + 1 : ℝ)) :=
      one_div_le_one_div_of_le hBpos hBn
    have h1B : |x n - a| < (1 / (B + 1 : ℝ)) := lt_of_lt_of_le hxlt h1n
    exact lt_trans h1B hBε

  have hfxto : TendsTo (fun n => f (x n)) L :=
    hSeq x hxane hxto

  rcases hfxto η hηpos with ⟨B, hB⟩
  have hlt : |f (x B) - L| < η := hB B (le_rfl)

  -- contradiction with construction
  have hge : η ≤ |f (x B) - L| := (hx B).2
  exact (not_lt_of_ge hge) hlt


-- equivalence of the three definitions

/-- `Limit_cycle f a L` collects the three fundamental implications
between the different standard definitions of the limit, which forms
a logical cycle. -/
theorem Limit_cycle (f : ℝ → ℝ) (a L : ℝ) :
    (LimitEpsDel f a L → LimitInterval f a L) ∧
    (LimitInterval f a L → LimitSeq f a L) ∧
    (LimitSeq f a L → LimitEpsDel f a L) := by
  refine ⟨LimitEpsDel_imp_LimitInterval (f:=f) (a:=a) (L:=L), ?_, ?_⟩
  exact LimitInterval_imp_LimitSeq (f:=f) (a:=a) (L:=L)
  exact LimitSeq_imp_LimitEpsDel (f:=f) (a:=a) (L:=L)

/-- `Limit_all_equiv f a L` states that the ε–δ, interval, and sequential
definitions of the limit are all logically equivalent. -/
theorem Limit_all_equiv (f : ℝ → ℝ) (a L : ℝ) :
    (LimitEpsDel f a L ↔ LimitInterval f a L) ∧
    (LimitInterval f a L ↔ LimitSeq f a L) ∧
    (LimitSeq f a L ↔ LimitEpsDel f a L) := by
  rcases Limit_cycle (f:=f) (a:=a) (L:=L) with ⟨hEI, hIS, hSE⟩
  refine ⟨?_, ?_, ?_⟩

  -- EpsDel ↔ Interval
  constructor
  exact hEI
  intro hI
  exact hSE (hIS hI)

  -- Interval ↔ Seq
  constructor
  exact hIS
  intro hS
  exact hEI (hSE hS)

  -- Seq ↔ EpsDel
  constructor
  exact hSE
  intro hE
  exact hIS (hEI hE)


#lint
