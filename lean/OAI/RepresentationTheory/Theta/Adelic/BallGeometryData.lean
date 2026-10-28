import OAI.RepresentationTheory.Theta.Adelic.BallNatural
import OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame
import OAI.RepresentationTheory.Theta.Adelic.RationalSU
import OAI.RepresentationTheory.Theta.Definitions

/-! # Ball Geometry Data -/

namespace OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

noncomputable section

/-!
Concrete geometric data for the complete AdelicTheta statement. The input consists
only of CM embeddings and orthonormal bases of the two Hermitian spaces.
There is no period map, oscillator lift, determinant comparison, or theta
identity in the input. All of those are conclusions in the statement.

AdelicSplitting uses a conjugate-linear first argument and (position,momentum) order.
The manuscript uses a linear first argument and (momentum,position) order.
Accordingly the skew form at the distinguished embedding is normalized to
-i times a positive Hermitian form. The positive Hodge subspace below is
L tensor P plus Ann(L) tensor P*, exactly as in PrescribedSigns.
-/

open scoped _root_.NumberField Classical _root_.Matrix Kronecker
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable (F : Type) [Field F] [NumberField F] (d : F) (m : ℕ)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

/-- Orthonormal CM coordinates. Giving such coordinates is a way of
specifying signature (2,1) at one place, definiteness at the other places,
and the one- or two-line multiplicity space. These are arithmetic and
Hermitian-form data, independent of every AdelicTheta conclusion. -/
structure BallArithmeticData where
  places : ℕ
  enumerate : Fin places ≃ NumberField.InfinitePlace F
  distinguished : Fin places
  other_place : ∃ v : Fin places, v ≠ distinguished
  real : ∀ v, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (enumerate v)) ≃+* ℝ
  real_continuous : ∀ v, Continuous (real v)
  real_inverse_continuous : ∀ v, Continuous (real v).symm
  complex : ∀ v, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (enumerate v)) ≃+* ℂ
  complex_continuous : ∀ v, Continuous (complex v)
  complex_inverse_continuous : ∀ v, Continuous (complex v).symm
  complex_scalar : ∀ v x,
    complex v (algebraMap _ _ x) = (real v x : ℂ)
  complex_star : ∀ v x, complex v (star x) = star (complex v x)
  basisV : Fin places → (Matrix (Fin 3) (Fin 3) ℂ)ˣ
  basisP : Fin places → (Matrix (Fin m) (Fin m) ℂ)ˣ
  positive : Fin places → Fin m → Bool
  distinguished_sign : ∀ j, positive distinguished j = false
  formV : ∀ v,
    (basisV v).val.conjTranspose *
        ((Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (enumerate v))).map (complex v)) *
          (basisV v).val =
      Matrix.diagonal (fun i : Fin 3 =>
        if v = distinguished ∧ i = 2 then (-1 : ℂ) else 1)
  formP : ∀ v,
    (basisP v).val.conjTranspose *
        ((Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (enumerate v))).map (complex v)) *
          (basisP v).val =
      Matrix.diagonal (fun j => if positive v j then Complex.I else -Complex.I)

variable {F d m H K}
variable (A : BallArithmeticData F d m H K)

abbrev FrameIndex := Fin A.places × (Fin 3 × Fin m)
abbrev ComplexPhase := Fin A.places →
  ((Fin 3 × Fin m → ℂ) × (Fin 3 × Fin m → ℂ))
abbrev RealPositions := Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)

/-- The actual standard representation in orthonormal V coordinates. -/
def standardMatrix (g : RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (A.basisV v).inv * ((g (A.enumerate v)).val.val.map (A.complex v)) *
    (A.basisV v).val

/-- The representation on V tensor P and its contragredient. P is a
multiplicity space, so SU(V) acts trivially on its index. -/
def geometricAction (g : RationalSU.ArchimedeanSU F H) (w : ComplexPhase A) : ComplexPhase A :=
  fun v =>
    (fun ij => ∑ k, standardMatrix A g v ij.1 k * (w v).1 (k, ij.2),
     fun ij => ∑ k, (standardMatrix A g v)⁻¹ k ij.1 * (w v).2 (k, ij.2))

/-- An explicit frame of the positive Hodge subspace. At the distinguished
place its columns are l(z) tensor e_j and the two annihilator columns
tensor e_j*. At a definite place each multiplicity line selects the whole
standard or dual summand according to its skew-Hermitian sign. -/
def geometricFrame (z : BallNatural.Ball) (a : FrameIndex A → ℂ) : ComplexPhase A :=
  fun v =>
    (fun ij => if v = A.distinguished then
        DeterminantCoordinates.lineVector z.val ij.1 * a (v, 0, ij.2)
      else if A.positive v ij.2 then a (v, ij) else 0,
     fun ij => if v = A.distinguished then
        DeterminantCoordinates.annihilatorVector z.val 0 ij.1 * a (v, 1, ij.2) +
          DeterminantCoordinates.annihilatorVector z.val 1 ij.1 * a (v, 2, ij.2)
      else if A.positive v ij.2 then 0 else a (v, ij))

/-- Coordinate extraction from the displayed Hodge frame. -/
def geometricCoordinates (w : ComplexPhase A) : FrameIndex A → ℂ :=
  fun vij => if vij.1 = A.distinguished then
    if vij.2.1 = 0 then (w vij.1).1 (2, vij.2.2)
    else if vij.2.1 = 1 then (w vij.1).2 (0, vij.2.2)
    else (w vij.1).2 (1, vij.2.2)
  else if A.positive vij.1 vij.2.2 then (w vij.1).1 vij.2 else (w vij.1).2 vij.2

/-- The Hodge subspace itself, without a chosen period map. -/
def HodgeSubspace (z : BallNatural.Ball) : Set (ComplexPhase A) :=
  Set.range (geometricFrame A z)

/-- The actual frame matrix of the tensor-product representation. -/
def frameMatrix (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    Matrix (FrameIndex A) (FrameIndex A) ℂ :=
  fun i j => geometricCoordinates A
    (geometricAction A g (geometricFrame A z (Pi.single j 1))) i

def dualFrameChange (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (v : FrameIndex A → ℂ) : FrameIndex A → ℂ :=
  (frameMatrix A g z)⁻¹ᵀ.mulVec v

/-- A real tensor vector, written in its standard and Hermitian-dual CM
components. The second component is the Hermitian identification of the
conjugate representation, not an independently chosen variable. -/
def realTensorComponents
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    ComplexPhase A :=
  fun v =>
    let x := ((A.basisV v).inv ⊗ₖ (A.basisP v).inv).mulVec
      (fun ij => A.complex v (s v ij))
    (x, fun ij =>
      (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive v ij.2 then (1 : ℂ) else -1) * star (x ij))

def archPositions (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) : RealPositions A :=
  fun v i => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x i))

/-- Literal principal congruence condition on the two F-coefficients of
each quadratic matrix entry. This is the coefficient lattice O_F + delta O_F in the
chosen E-basis; these levels are cofinal among compact open levels. -/
def PrincipalLevel (N : ℕ) (g : SpecialUnitary.SU H.val) : Prop :=
  ∀ i j, ∃ a b : 𝓞 F,
    g.val.val i j - (1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j =
      (N : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) *
        (⟨(a : F), (b : F)⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)

def ballDomain : Set (Fin 2 → ℂ) :=
  {z | Complex.normSq (z 0) + Complex.normSq (z 1) < 1}

/-- Smoothness on the ball, expressed in its actual affine chart. -/
def BallSmooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : BallNatural.Ball → V) : Prop :=
  ContDiffOn ℝ ⊤ (fun z => if hz : z ∈ ballDomain then f ⟨z, hz⟩ else 0) ballDomain

/-- Holomorphicity in the affine ball chart. -/
def BallHolomorphic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : BallNatural.Ball → V) : Prop :=
  DifferentiableOn ℂ (fun z => if hz : z ∈ ballDomain then f ⟨z, hz⟩ else 0) ballDomain

end

end OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
