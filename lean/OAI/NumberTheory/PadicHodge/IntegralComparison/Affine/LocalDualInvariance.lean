import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualInvariance

/-! # Local Dual Invariance -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalDualInvariance

noncomputable section

/-! An identity lift between resolutions which are projective on an
affine open cover induces a quasi-isomorphism of internal Hom complexes.
The conclusion concerns the actual sheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (N : X.Modules)

def functor : (ChainComplex X.Modules ℕ)ᵒᵖ ⥤ CochainComplex X.Modules ℕ :=
  HomologicalComplex.opFunctor X.Modules (.down ℕ) ⋙
    (SchemeInternalHom.functor N).mapHomologicalComplex (ComplexShape.down ℕ).symm

variable (M : X.Modules) [M.IsQuasicoherent] (K L : ChainComplex X.Modules ℕ)
  [∀ n, (K.X n).IsQuasicoherent] [∀ n, (L.X n).IsQuasicoherent]
  [∀ n, (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X n) N).IsQuasicoherent]
  [∀ n, (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (L.X n) N).IsQuasicoherent]
  (εK : K ⟶ (ChainComplex.single₀ X.Modules).obj M)
  (εL : L ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso εK] [QuasiIso εL]
  (a : K ⟶ L) (ha : a ≫ εL = εK)

include ha in
theorem quasiIso {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    (hK : ∀ i n, Projective ((AffineOpen.InternalHom.sections (U i) (hAffine i)).obj (K.X n)))
    (hL : ∀ i n, Projective ((AffineOpen.InternalHom.sections (U i) (hAffine i)).obj (L.X n))) :
    QuasiIso ((functor N).map a.op) := by
  let (n : ℕ) : (((functor N).obj (op K)).X n).IsQuasicoherent :=
    inferInstanceAs (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X n) N).IsQuasicoherent
  let (n : ℕ) : (((functor N).obj (op L)).X n).IsQuasicoherent :=
    inferInstanceAs (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (L.X n) N).IsQuasicoherent
  apply LocalQuasiIso.of_cover ((functor N).map a.op) U hU hAffine
  intro i
  let (n : ℕ) := hK i n
  let (n : ℕ) := hL i n
  exact ResolutionDualInvariance.native_quasiIso
    (U i) (hAffine i) N M K L εK εL a ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalDualInvariance
