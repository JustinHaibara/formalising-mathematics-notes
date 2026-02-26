import Mathlib


-- Gaussian integers Γ

/-- `GaussInt` is the structure of Gaussian integers
where `(x, y) = x+iy` will be implemented as `⟨x, y⟩`. -/
structure GaussInt where
  /-- `re` is the real part of a Gaussian integer. -/
  re : ℤ
  /-- `im` is the imaginary part of a Gaussian integer. -/
  im : ℤ

namespace GaussInt

-- basic operations

/-- `zero` is the Gaussian integer `(0, 0)`. -/
def zero : GaussInt := ⟨0, 0⟩
/-- `one` is the Gaussian integer `(1, 0)`. -/
def one  : GaussInt := ⟨1, 0⟩

/-- `add` is the addition of Gaussian integers
where `(x, y) + (u, v) = (x+u, y+v)`. -/
def add (z w : GaussInt) : GaussInt :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- `neg` is the negation of a Gaussian integer
where `-(x, y) = (-x, -y)`. -/
def neg (z : GaussInt) : GaussInt := ⟨-z.re, -z.im⟩

/-- `mul` is the multiplication of Gaussian integers
where `(x, y) * (u, v) = (xu - yv, xv + yu)`. -/
def mul (z w : GaussInt) : GaussInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

instance : Zero GaussInt := ⟨zero⟩
instance : One GaussInt := ⟨one⟩
instance : Add GaussInt := ⟨add⟩
instance : Neg GaussInt := ⟨neg⟩
instance : Mul GaussInt := ⟨mul⟩


-- ext lemma

@[ext] lemma ext (z w : GaussInt)
    (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  cases z
  cases w
  cases hr
  cases hi
  rfl

-- simp lemmas

@[simp, nolint simpVarHead] lemma re_mk (a b : ℤ) :
    (GaussInt.mk a b).re = a := rfl
@[simp, nolint simpVarHead] lemma im_mk (a b : ℤ) :
    (GaussInt.mk a b).im = b := rfl

@[simp] lemma re_zero : (0 : GaussInt).re = 0 := rfl
@[simp] lemma im_zero : (0 : GaussInt).im = 0 := rfl
@[simp] lemma re_one : (1 : GaussInt).re = 1 := rfl
@[simp] lemma im_one : (1 : GaussInt).im = 0 := rfl

@[simp] lemma re_add (z w : GaussInt) :
    (z + w).re = z.re + w.re := rfl
@[simp] lemma im_add (z w : GaussInt) :
    (z + w).im = z.im + w.im := rfl

@[simp] lemma re_neg (z : GaussInt) :
    (-z).re = -z.re := rfl
@[simp] lemma im_neg (z : GaussInt) :
    (-z).im = -z.im := rfl

@[simp] lemma re_mul (z w : GaussInt) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma im_mul (z w : GaussInt) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl


-- additive laws

lemma add_assoc (a b c : GaussInt) :
    a + b + c = a + (b + c) := by
  ext <;> simp <;> ring
lemma add_comm (a b : GaussInt) :
    a + b = b + a := by
  ext <;> simp <;> ring

lemma zero_add (a : GaussInt) :
    0 + a = a := by
  ext <;> simp
lemma add_zero (a : GaussInt) :
    a + 0 = a := by
  ext <;> simp
lemma neg_add_cancel (a : GaussInt) :
    -a + a = 0 := by
  ext <;> simp

-- multiplicative laws

lemma mul_assoc (a b c : GaussInt) :
    a * b * c = a * (b * c) := by
  ext <;> simp <;> ring
lemma mul_comm (a b : GaussInt) :
    a * b = b * a := by
  ext <;> simp <;> ring

lemma zero_mul (a : GaussInt) :
    0 * a = 0 := by
  ext <;> simp
lemma mul_zero (a : GaussInt) :
    a * 0 = 0 := by
  ext <;> simp

lemma one_mul (a : GaussInt) :
    1 * a = a := by
  ext <;> simp
lemma mul_one (a : GaussInt) :
    a * 1 = a := by
  ext <;> simp

lemma left_distrib (a b c : GaussInt) :
    a * (b + c) = a * b + a * c := by
  ext <;> simp <;> ring
lemma right_distrib (a b c : GaussInt) :
    (a + b) * c = a * c + b * c := by
  ext <;> simp <;> ring

-- commutative ring structure

instance : CommRing GaussInt where
  add := (· + ·)
  add_assoc := add_assoc
  add_comm := add_comm

  zero := 0
  zero_add := zero_add
  add_zero := add_zero

  neg := Neg.neg
  neg_add_cancel := neg_add_cancel

  nsmul := nsmulRec
  zsmul := zsmulRec

  mul := (· * ·)
  mul_assoc := mul_assoc
  mul_comm := mul_comm

  zero_mul := zero_mul
  mul_zero := mul_zero

  one := 1
  one_mul := one_mul
  mul_one := mul_one

  left_distrib := left_distrib
  right_distrib := right_distrib


-- norm on Γ

/-- `norm` is the norm of a Gaussian integer
where `N(x, y) = x^2 + y^2`. -/
def norm (z : GaussInt) : ℕ :=
  Int.toNat (z.re^2 + z.im^2)

-- non-negativity

lemma norm_nonneg (z : GaussInt) :
    0 ≤ z.re^2 + z.im^2 := by
  have h1 : 0 ≤ z.re^2 := sq_nonneg _
  have h2 : 0 ≤ z.im^2 := sq_nonneg _
  exact add_nonneg h1 h2

-- multiplicativity

lemma norm_mul (z w : GaussInt) :
    norm (z * w) = norm z * norm w := by
  unfold norm
  have h :
    (z * w).re^2 + (z * w).im^2
      = (z.re^2 + z.im^2) * (w.re^2 + w.im^2) := by
    simp ; ring

  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z * w)
  simp_all [Int.toNat_mul]

-- norm detects zero

lemma norm_eq_zero_iff (z : GaussInt) :
    norm z = 0 ↔ z = 0 := by
  unfold norm
  constructor

  · intro h0
    set t : ℤ := z.re^2 + z.im^2

    have ht_nonneg : 0 ≤ t := by
      simpa [t] using norm_nonneg z
    have ht_nonpos : t ≤ 0 := by
      have : Int.toNat t = 0 := by simpa [t] using h0
      exact (Int.toNat_eq_zero).1 this
    have ht_zero : t = 0 :=
      le_antisymm ht_nonpos ht_nonneg

    have hre_nonneg : 0 ≤ z.re^2 := sq_nonneg _
    have him_nonneg : 0 ≤ z.im^2 := sq_nonneg _
    have heq : z.re^2 = 0 ∧ z.im^2 = 0 := by
      have : z.re^2 + z.im^2 = 0 := by
        simpa [t] using ht_zero
      exact
        (add_eq_zero_iff_of_nonneg
          hre_nonneg him_nonneg).1 this

    have hre : z.re = 0 := sq_eq_zero_iff.1 heq.1
    have him : z.im = 0 := sq_eq_zero_iff.1 heq.2

    ext <;> simp [hre, him]

  · intro hz
    subst hz
    simp

lemma norm_ne_zero (z : GaussInt) (hz : z ≠ 0) :
    norm z ≠ 0 := by
  intro h
  exact hz ((norm_eq_zero_iff z).1 h)

end GaussInt


-- Gaussian ratonals

/-- `GaussRat` is the structure of Gaussian rationals
where `(x, y) = x+iy` will be implemented as `⟨x, y⟩`. -/
structure GaussRat where
  /-- `re` is the real part. -/
  re : ℚ
  /-- `im` is the imaginary part. -/
  im : ℚ

namespace GaussRat

/-- `zero` is `(0, 0)`. -/
def zero : GaussRat := ⟨0, 0⟩
/-- `one` is `(1, 0)`. -/
def one  : GaussRat := ⟨1, 0⟩
/-- Addition: `(x, y) + (u, v) = (x+u, y+v)`. -/
def add (z w : GaussRat) : GaussRat :=
  ⟨z.re + w.re, z.im + w.im⟩
/-- Negation: `-(x, y) = (-x, -y)`. -/
def neg (z : GaussRat) : GaussRat := ⟨-z.re, -z.im⟩
/-- Multiplication: `(x, y) * (u, v) = (xu - yv, xv + yu)`. -/
def mul (z w : GaussRat) : GaussRat :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

instance : Zero GaussRat := ⟨zero⟩
instance : One  GaussRat := ⟨one⟩
instance : Add  GaussRat := ⟨add⟩
instance : Neg  GaussRat := ⟨neg⟩
instance : Mul  GaussRat := ⟨mul⟩

@[ext] lemma ext (z w : GaussRat)
    (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  cases z
  cases w
  cases hr
  cases hi
  rfl

@[simp] lemma re_zero : (0 : GaussRat).re = 0 := rfl
@[simp] lemma im_zero : (0 : GaussRat).im = 0 := rfl
@[simp] lemma re_one : (1 : GaussRat).re = 1 := rfl
@[simp] lemma im_one : (1 : GaussRat).im = 0 := rfl
@[simp] lemma re_add (z w : GaussRat) :
    (z + w).re = z.re + w.re := rfl
@[simp] lemma im_add (z w : GaussRat) :
    (z + w).im = z.im + w.im := rfl
@[simp] lemma re_neg (z : GaussRat) :
    (-z).re = -z.re := rfl
@[simp] lemma im_neg (z : GaussRat) :
    (-z).im = -z.im := rfl
@[simp] lemma re_mul (z w : GaussRat) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma im_mul (z w : GaussRat) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

lemma add_assoc (a b c : GaussRat) :
    a + b + c = a + (b + c) := by
  ext <;> simp <;> ring
lemma add_comm (a b : GaussRat) :
    a + b = b + a := by
  ext <;> simp <;> ring
lemma zero_add (a : GaussRat) :
    0 + a = a := by
  ext <;> simp
lemma add_zero (a : GaussRat) :
    a + 0 = a := by
  ext <;> simp
lemma neg_add_cancel (a : GaussRat) :
    -a + a = 0 := by
  ext <;> simp

lemma mul_assoc (a b c : GaussRat) :
    a * b * c = a * (b * c) := by
  ext <;> simp <;> ring
lemma mul_comm (a b : GaussRat) :
    a * b = b * a := by
  ext <;> simp <;> ring
lemma zero_mul (a : GaussRat) :
    0 * a = 0 := by
  ext <;> simp
lemma mul_zero (a : GaussRat) :
    a * 0 = 0 := by
  ext <;> simp
lemma one_mul (a : GaussRat) :
    1 * a = a := by
  ext <;> simp
lemma mul_one (a : GaussRat) :
    a * 1 = a := by
  ext <;> simp
lemma left_distrib (a b c : GaussRat) :
    a * (b + c) = a * b + a * c := by
  ext <;> simp <;> ring
lemma right_distrib (a b c : GaussRat) :
    (a + b) * c = a * c + b * c := by
  ext <;> simp <;> ring

instance : CommRing GaussRat where
  add := (· + ·)
  add_assoc := add_assoc
  add_comm := add_comm
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  neg := Neg.neg
  neg_add_cancel := neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul := (· * ·)
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  zero_mul := zero_mul
  mul_zero := mul_zero
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib

end GaussRat


-- embedding

/-- The natural embedding `GaussInt → GaussRat`
sending `(a,b)` to `(a,b)` with coercions `ℤ → ℚ`. -/
def GaussInt.toGaussRat (z : GaussInt) : GaussRat :=
  ⟨(z.re : ℚ), (z.im : ℚ)⟩

namespace GaussInt

@[simp] lemma toGaussRat_re (z : GaussInt) :
    (toGaussRat z).re = (z.re : ℚ) := rfl
@[simp] lemma toGaussRat_im (z : GaussInt) :
    (toGaussRat z).im = (z.im : ℚ) := rfl

@[simp] lemma toGaussRat_zero :
    toGaussRat (0 : GaussInt) = (0 : GaussRat) := by
  ext <;> simp
@[simp] lemma toGaussRat_one :
    toGaussRat (1 : GaussInt) = (1 : GaussRat) := by
  ext <;> simp

@[simp] lemma toGaussRat_add (z w : GaussInt) :
  toGaussRat (z + w)
    = (toGaussRat z + toGaussRat w : GaussRat) := by
  ext <;> simp

@[simp] lemma toGaussRat_neg (z : GaussInt) :
    toGaussRat (-z) = (-toGaussRat z : GaussRat) := by
  ext <;> simp

@[simp] lemma toGaussRat_mul (z w : GaussInt) :
  toGaussRat (z * w)
    = (toGaussRat z * toGaussRat w : GaussRat) := by
  ext <;> simp

-- embedding preserves zero

lemma toGaussRat_eq_zero_iff (z : GaussInt) :
    toGaussRat z = (0 : GaussRat) ↔ z = 0 := by
  constructor

  · intro h0
    have hre0 : (toGaussRat z).re = 0 := by simp [h0]
    have him0 : (toGaussRat z).im = 0 := by simp [h0]

    have hreQ : (z.re : ℚ) = 0 := by
      simpa [GaussInt.toGaussRat] using hre0
    have himQ : (z.im : ℚ) = 0 := by
      simpa [GaussInt.toGaussRat] using him0

    have hreZ : z.re = 0 := by exact_mod_cast hreQ
    have himZ : z.im = 0 := by exact_mod_cast himQ

    ext <;> simp [hreZ, himZ]

  · intro hz
    subst hz
    simp

lemma toGaussRat_ne_zero (z : GaussInt) (hz : z ≠ 0) :
    toGaussRat z ≠ (0 : GaussRat) := by
  intro h
  exact hz ((toGaussRat_eq_zero_iff z).1 h)


-- embedding is a ring homomorphism

/-- The natural embedding `GaussInt →+* GaussRat`
as ring homomorphism. -/
def toGaussRatRingHom : GaussInt →+* GaussRat where
  toFun := toGaussRat
  map_one' := by simp
  map_zero' := by simp
  map_add' z w := by simp
  map_mul' z w := by simp

@[simp] lemma toGaussRatRingHom_apply (z : GaussInt) :
    toGaussRatRingHom z = toGaussRat z := rfl

@[simp] lemma toGaussRat_sub (z w : GaussInt) :
  toGaussRat (z - w)
    = (toGaussRat z - toGaussRat w : GaussRat) := by
  simp [sub_eq_add_neg]

end GaussInt


-- conjugate

namespace GaussRat

/-- `conj` is complex conjugation: `conj(x,y) = (x, -y)`. -/
def conj (z : GaussRat) : GaussRat := ⟨z.re, -z.im⟩

@[simp] lemma conj_re (z : GaussRat) :
    (conj z).re = z.re := rfl
@[simp] lemma conj_im (z : GaussRat) :
    (conj z).im = -z.im := rfl

@[simp] lemma conj_conj (z : GaussRat) :
    conj (conj z) = z := by
  ext <;> simp


-- norm on Gaussian rationals

/-- `norm` is the norm: `x^2 + y^2`. -/
def norm (z : GaussRat) : ℚ := z.re^2 + z.im^2

lemma norm_nonneg (z : GaussRat) :
    0 ≤ z.re^2 + z.im^2 := by
  have h1 : 0 ≤ z.re^2 := sq_nonneg _
  have h2 : 0 ≤ z.im^2 := sq_nonneg _
  exact add_nonneg h1 h2

lemma norm_mul (z w : GaussRat) :
    norm (z * w) = norm z * norm w := by
  unfold norm
  have h :
    (z * w).re^2 + (z * w).im^2
      = (z.re^2 + z.im^2) * (w.re^2 + w.im^2) := by
    simp ; ring

  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z * w)
  simp_all

lemma norm_eq_zero_iff (z : GaussRat) :
    norm z = 0 ↔ z = 0 := by
  unfold norm
  constructor
  · intro h0
    have hre_nonneg : 0 ≤ z.re^2 := sq_nonneg _
    have him_nonneg : 0 ≤ z.im^2 := sq_nonneg _
    have heq : z.re^2 = 0 ∧ z.im^2 = 0 :=
      (add_eq_zero_iff_of_nonneg
        hre_nonneg him_nonneg).1 h0
    have hre : z.re = 0 := sq_eq_zero_iff.1 heq.1
    have him : z.im = 0 := sq_eq_zero_iff.1 heq.2
    ext <;> simp [hre, him]
  · intro hz
    subst hz
    simp

lemma norm_ne_zero (z : GaussRat) (hz : z ≠ 0) :
    norm z ≠ 0 := by
  intro h
  exact hz ((norm_eq_zero_iff z).1 h)


-- inverse

/-- `inv` is the inverse in `ℚ(i)`:
`inv(z) = conj(z) / N(z)`. -/
def inv (z : GaussRat) : GaussRat :=
  ⟨(conj z).re / norm z, (conj z).im / norm z⟩

instance : Inv GaussRat := ⟨inv⟩

@[simp] lemma inv_re (z : GaussRat) :
    (z⁻¹).re = z.re / norm z := rfl
@[simp] lemma inv_im (z : GaussRat) :
    (z⁻¹).im = (-z.im) / norm z := rfl


-- division

/-- Define division by `z / w = z * w⁻¹`. -/
def div (z w : GaussRat) : GaussRat := z * w⁻¹

instance : Div GaussRat := ⟨div⟩

@[simp] lemma div_def (z w : GaussRat) :
    z / w = z * w⁻¹ := rfl

end GaussRat


-- rounding in ℚ

namespace GaussRat

/-- Nearest integer to a rational number
via `floor(x + 1/2)`. -/
def roundInt (x : ℚ) : ℤ :=
  Int.floor (x + 1/2)

theorem abs_sub_roundInt_le (x : ℚ) :
    |x - (roundInt x : ℚ)| ≤ 1/2 := by
  unfold roundInt
  set n := Int.floor (x + 1/2)

  have hfloor :
      n ≤ x + 1/2 ∧ x + 1/2 < n + 1 := by
    exact
      ⟨Int.floor_le (x + 1/2),
        Int.lt_floor_add_one (x + 1/2)⟩

  rcases hfloor with ⟨h1, h2⟩

  have hleft : -(1/2) ≤ x - n := by
    have := h1
    linarith
  have hright : x - n ≤ 1/2 := by
    have := h2
    linarith

  exact abs_le.mpr ⟨hleft, hright⟩


-- rounding GaussRat to GaussInt

/-- Round a Gaussian rational to
a Gaussian integer by rounding components. -/
def roundGaussInt (z : GaussRat) : GaussInt :=
  ⟨roundInt z.re, roundInt z.im⟩

lemma abs_re_sub_roundGaussInt_le (z : GaussRat) :
    |z.re - ((roundGaussInt z).re : ℚ)| ≤ 1/2 := by
  simpa [roundGaussInt, roundInt]
    using abs_sub_roundInt_le z.re

lemma abs_im_sub_roundGaussInt_le (z : GaussRat) :
    |z.im - ((roundGaussInt z).im : ℚ)| ≤ 1/2 := by
  simpa [roundGaussInt, roundInt]
    using abs_sub_roundInt_le z.im

end GaussRat


-- quotient and remainder for Euclidean division

namespace GaussInt

/-- The quotient for Euclidean division:
round `(a/b)` in `GaussRat`. -/
def euclidQuot (a b : GaussInt) : GaussInt :=
  GaussRat.roundGaussInt (toGaussRat a / toGaussRat b)

/-- The remainder: `r = a - b*q`. -/
def euclidRem (a b : GaussInt) : GaussInt :=
  a - b * euclidQuot a b

lemma euclid_decomp (a b : GaussInt) :
    a = b * euclidQuot a b + euclidRem a b := by
  simp [euclidRem]

end GaussInt


-- key bound for rounding in Gaussian rartionals

namespace GaussRat

lemma sq_le_of_abs_le (x a : ℚ) (h : |x| ≤ a) :
    x^2 ≤ a^2 := by
  have habs : |x| * |x| ≤ a * a := by
    have hx : 0 ≤ |x| := abs_nonneg x
    have ha : 0 ≤ a := le_trans hx h
    exact mul_le_mul h h hx ha
  simpa [pow_two, abs_mul_self] using habs

lemma sq_dist_roundGaussInt_le (z : GaussRat) :
  (z.re - ((roundGaussInt z).re : ℚ))^2
    + (z.im - ((roundGaussInt z).im : ℚ))^2 ≤ 1/2 := by

  have hre :
      |z.re - ((roundGaussInt z).re : ℚ)| ≤ 1/2 :=
    abs_re_sub_roundGaussInt_le z
  have him :
      |z.im - ((roundGaussInt z).im : ℚ)| ≤ 1/2 :=
    abs_im_sub_roundGaussInt_le z

  have hre2 :
      (z.re - ((roundGaussInt z).re : ℚ))^2 ≤ (1/2)^2 :=
    sq_le_of_abs_le
      (z.re - ((roundGaussInt z).re : ℚ)) (1/2) hre
  have him2 :
      (z.im - ((roundGaussInt z).im : ℚ))^2 ≤ (1/2)^2 :=
    sq_le_of_abs_le
      (z.im - ((roundGaussInt z).im : ℚ)) (1/2) him

  have hsum :
    (z.re - ((roundGaussInt z).re : ℚ))^2
      + (z.im - ((roundGaussInt z).im : ℚ))^2
        ≤ (1/2)^2 + (1/2)^2 :=
    add_le_add hre2 him2

  have hhalf : ((1/2)^2 + (1/2)^2) = 1/2 := by ring
  linarith


theorem norm_sub_roundGaussInt_le (z : GaussRat) :
  norm (z - GaussInt.toGaussRat (roundGaussInt z))
    ≤ 1/2 := by
  simpa [GaussRat.norm, sub_eq_add_neg] using
    (sq_dist_roundGaussInt_le z)

end GaussRat


-- embedding of remainder

namespace GaussInt
open GaussRat

lemma mul_div_cancel_toGaussRat
  (a b : GaussInt) (hb : b ≠ 0) :
    (toGaussRat b)
      * (toGaussRat a / toGaussRat b) = toGaussRat a := by
  have hbQ : toGaussRat b ≠ (0 : GaussRat) :=
    toGaussRat_ne_zero b hb
  have hn : GaussRat.norm (toGaussRat b) ≠ 0 :=
    GaussRat.norm_ne_zero (toGaussRat b) hbQ

  ext <;>
  simp [GaussRat.div_def, GaussRat.norm] <;>
  field_simp [hn] <;>
  ring_nf
  · set t : ℚ := (↑b.re : ℚ)^2 + (↑b.im : ℚ)^2
    have ht : t ≠ 0 :=
      by simpa [GaussRat.norm, t] using hn
    calc
      (↑b.re : ℚ)^2 * (↑a.re : ℚ) * t⁻¹
        + (↑a.re : ℚ) * (↑b.im : ℚ)^2 * t⁻¹
          = (↑a.re : ℚ)
            * ((↑b.re : ℚ)^2 + (↑b.im : ℚ)^2) * t⁻¹ := by
              ring
      _   = (↑a.re : ℚ) * t * t⁻¹ := by simp [t]
      _   = (↑a.re : ℚ) := by
              simp [ht]

  · set t : ℚ := (↑b.re : ℚ)^2 + (↑b.im : ℚ)^2
    have ht : t ≠ 0 :=
      by simpa [GaussRat.norm, t] using hn
    calc
      (↑b.re : ℚ)^2 * (↑a.im : ℚ) * t⁻¹
        + (↑b.im : ℚ)^2 * (↑a.im : ℚ) * t⁻¹
          = (↑a.im : ℚ)
            * ((↑b.re : ℚ)^2 + (↑b.im : ℚ)^2) * t⁻¹ := by
              ring
      _   = (↑a.im : ℚ) * t * t⁻¹ := by simp [t]
      _   = (↑a.im : ℚ) := by
              simp [ht]


theorem toGaussRat_euclidRem (a b : GaussInt) (hb : b ≠ 0) :
  toGaussRat (euclidRem a b) = toGaussRat b
    * (toGaussRat a / toGaussRat b - toGaussRat (euclidQuot a b)) := by
  have hb_cancel : (toGaussRat b)
      * (toGaussRat a * (toGaussRat b)⁻¹) = toGaussRat a :=
    mul_div_cancel_toGaussRat a b hb

  unfold euclidRem
  calc
    toGaussRat (a - b * euclidQuot a b)
        = toGaussRat a - toGaussRat (b * euclidQuot a b) := by
          simp
    _   = toGaussRat a
          - (toGaussRat b * toGaussRat (euclidQuot a b)) := by
            simp [toGaussRat_mul]
    _   = (toGaussRat b * (toGaussRat a / toGaussRat b))
          - (toGaussRat b * toGaussRat (euclidQuot a b)) := by
            simp [hb_cancel]
    _   = toGaussRat b
          * (toGaussRat a / toGaussRat b - toGaussRat (euclidQuot a b)) := by
            simp [sub_eq_add_neg, mul_add]


-- Euclidean inequality

theorem norm_toGaussRat_euclidRem_lt
  (a b : GaussInt) (hb : b ≠ 0) :
    GaussRat.norm (toGaussRat (euclidRem a b))
      < GaussRat.norm (toGaussRat b) := by

  have hbQ : toGaussRat b ≠ (0 : GaussRat) :=
    toGaussRat_ne_zero b hb
  have hnpos : 0 < GaussRat.norm (toGaussRat b) := by
    have hn0 : GaussRat.norm (toGaussRat b) ≠ 0 :=
      GaussRat.norm_ne_zero (toGaussRat b) hbQ
    have hnonneg : 0 ≤ GaussRat.norm (toGaussRat b) := by
      simp [GaussRat.norm, add_nonneg, sq_nonneg]
    exact lt_of_le_of_ne hnonneg (Ne.symm hn0)

  set z : GaussRat := toGaussRat a / toGaussRat b

  have hrem :
    toGaussRat (euclidRem a b) = toGaussRat b
        * (z - toGaussRat (euclidQuot a b)) := by
      simpa [z] using (toGaussRat_euclidRem a b hb)

  have hnorm :
    GaussRat.norm (toGaussRat (euclidRem a b))
      = GaussRat.norm (toGaussRat b)
        * GaussRat.norm (z - toGaussRat (euclidQuot a b)) := by
      calc
        GaussRat.norm (toGaussRat (euclidRem a b))
            = GaussRat.norm (toGaussRat b * (z - toGaussRat (euclidQuot a b))) := by
                simp [hrem]
        _   = GaussRat.norm (toGaussRat b)
              * GaussRat.norm (z - toGaussRat (euclidQuot a b)) := by
                simpa using
                  (GaussRat.norm_mul (toGaussRat b) (z - toGaussRat (euclidQuot a b)))

  have hbound :
    GaussRat.norm (z - toGaussRat (euclidQuot a b))
      ≤ 1/2 := by
    simpa [GaussInt.euclidQuot, z]
      using (GaussRat.norm_sub_roundGaussInt_le z)

  have hle : GaussRat.norm (toGaussRat (euclidRem a b))
      ≤ GaussRat.norm (toGaussRat b) * (1/2) := by
    have hbnonneg : 0 ≤ GaussRat.norm (toGaussRat b) := by
      simp [GaussRat.norm, add_nonneg, sq_nonneg]
    calc
      GaussRat.norm (toGaussRat (euclidRem a b))
          = GaussRat.norm (toGaussRat b)
            * GaussRat.norm (z - toGaussRat (euclidQuot a b)) :=
              hnorm
      _   ≤ GaussRat.norm (toGaussRat b) * (1/2) := by
              exact mul_le_mul_of_nonneg_left hbound hbnonneg

  have hlhalf : GaussRat.norm (toGaussRat b) * (1/2)
      < GaussRat.norm (toGaussRat b) := by
    linarith

  exact lt_of_le_of_lt hle hlhalf

end GaussInt


#lint
