import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.LiftIso

/-! # Resolution Dual Invariance -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualInvariance

noncomputable section

/-! An actual identity lift between affine-projective sheaf resolutions
preserves the native internal-Hom cohomology on that affine open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (N M : X.Modules)
  [M.IsQuasicoherent] (K L : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent] [∀ i, (L.X i).IsQuasicoherent]
  (εK : K ⟶ (ChainComplex.single₀ X.Modules).obj M)
  (εL : L ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso εK] [QuasiIso εL]
  [∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X i))]
  (a : K ⟶ L) (ha : a ≫ εL = εK)

def algebraicMap :=
  ((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map a

include ha in
theorem algebraicMap_augmentation :
    algebraicMap U hU K L a ≫ (AffineOpen.Resolution.ofAugmentation U hU M L εL).π =
      (AffineOpen.Resolution.ofAugmentation U hU M K εK).π := by
  let F := (AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)
  change F.map a ≫ (F.map εL ≫ _) = F.map εK ≫ _
  rw [← Category.assoc, ← F.map_comp, ha]

def nativeFunctor : (ChainComplex X.Modules ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat Γ(X, U)) ℕ :=
  HomologicalComplex.opFunctor X.Modules (.down ℕ) ⋙
    (AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm

include hU εK εL ha in
theorem native_quasiIso : QuasiIso ((nativeFunctor U N).map a.op) := by
  let PK := AffineOpen.Resolution.ofAugmentation U hU M K εK
  let PL := AffineOpen.Resolution.ofAugmentation U hU M L εL
  let F := (linearYoneda Γ(X, U) (ModuleCat Γ(X, U))).obj
    ((AffineOpen.InternalHom.sections U hU).obj N)
  let b := algebraicMap U hU K L a
  have hb : b ≫ PL.π = PK.π := algebraicMap_augmentation U hU M K L εK εL a ha
  have hAlg := ProjectiveResolution.LiftIso.quasiIso F PK PL b hb
  let G := HomologicalComplex.opFunctor X.Modules (.down ℕ) ⋙
    (AffineOpen.LinearHom.algebraicHom U hU N).mapHomologicalComplex (ComplexShape.down ℕ).symm
  let : QuasiIso (G.map a.op) := hAlg
  let (i : ℕ) : (K.op.X i).unop.IsQuasicoherent := inferInstanceAs (K.X i).IsQuasicoherent
  let (i : ℕ) : (L.op.X i).unop.IsQuasicoherent := inferInstanceAs (L.X i).IsQuasicoherent
  let eK := AffineOpen.LinearHom.complexIso U hU N (ComplexShape.down ℕ).symm K.op
  let eL := AffineOpen.LinearHom.complexIso U hU N (ComplexShape.down ℕ).symm L.op
  have hn : (nativeFunctor U N).map a.op ≫ eK.hom = eL.hom ≫ G.map a.op :=
    ((AffineOpen.LinearHom.comparison U hU N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).naturality ((HomologicalComplex.opFunctor X.Modules (.down ℕ)).map a.op)
  have : QuasiIso ((nativeFunctor U N).map a.op ≫ eK.hom) := by
    rw [hn]
    infer_instance
  exact quasiIso_of_comp_right _ eK.hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualInvariance
