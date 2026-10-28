import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeExact
import OAI.AlgebraicGeometry.Picard.PoincareBundle.BeckDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification

/-! # Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Invariant

noncomputable section

/-!
# Effective geometric affine invariant sheaves for PoincareBundle

Flat affine pullback preserves the defining invariant equalizer of a
quasi-coherent coaction. Thus the canonical invariant sheaf recovers the
supplied geometric descent datum. Faithful flatness descends its line property.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
  (D : BeckDescent.SheafDatum (Spec.map f))

/-- Both terms of the invariant equalizer are quasi-coherent. -/
theorem invariantDiagram_isQuasicoherent [D.A.IsQuasicoherent]
    (j : WalkingParallelPair) :
    ((parallelPair ((Scheme.Modules.pushforward (Spec.map f)).map D.a)
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app _)).obj j).IsQuasicoherent := by
  have h₀ := QuasiCoherent.pushforward_isQuasicoherent f D.A
  have h₁ := QuasiCoherent.pullback_isQuasicoherent f
    ((Scheme.Modules.pushforward (Spec.map f)).obj D.A)
  cases j with
  | zero => exact h₀
  | one =>
      exact @QuasiCoherent.pushforward_isQuasicoherent _ _ f _ h₁

/-- The actual invariant equalizer is a quasi-coherent module sheaf. -/
theorem invariantSheaf_isQuasicoherent [D.A.IsQuasicoherent] :
    (BeckDescent.invariantSheaf (Spec.map f) D).IsQuasicoherent :=
  TildeExact.limit_isQuasicoherent _ (invariantDiagram_isQuasicoherent f D)

/-- Flat affine pullback recovers a geometric quasi-coherent coaction
from its raw invariant sheaf. -/
theorem invariantComparison_isIso (hf : f.hom.Flat) [D.A.IsQuasicoherent] :
    IsIso (BeckDescent.invariantComparison (Spec.map f) D).f := by
  have := TildeExact.pullback_preserves_diagram f hf _
    (invariantDiagram_isQuasicoherent f D)
  exact BeckDescent.invariantComparison_isIso_of_preservesEqualizer (Spec.map f) D

/-- The canonical pullback identification of the invariant sheaf. -/
def invariantPullbackIso (hf : f.hom.Flat) [D.A.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map f)).obj
      (BeckDescent.invariantSheaf (Spec.map f) D) ≅ D.A := by
  let a := (BeckDescent.invariantComparison (Spec.map f) D).f
  have ha : IsIso a := invariantComparison_isIso f D hf
  exact @asIso _ _ _ _ a ha

/-- The invariant module sheaf is recovered from its global sections. -/
def invariantTildeIso [D.A.IsQuasicoherent] :
    tilde ((moduleSpecΓFunctor (R := R)).obj
      (BeckDescent.invariantSheaf (Spec.map f) D)) ≅
        BeckDescent.invariantSheaf (Spec.map f) D := by
  have := invariantSheaf_isQuasicoherent f D
  let a := Scheme.Modules.fromTildeΓ (R := R)
    (BeckDescent.invariantSheaf (Spec.map f) D)
  have ha : IsIso a := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) _
  exact @asIso _ _ _ _ a ha

/-- The scalar extension of invariant global sections has associated sheaf
equal to the original geometric module sheaf. -/
def extendedInvariantTildeIso (hf : f.hom.Flat) [D.A.IsQuasicoherent] :
    tilde ((ModuleCat.extendScalars f.hom).obj ((moduleSpecΓFunctor (R := R)).obj
      (BeckDescent.invariantSheaf (Spec.map f) D))) ≅ D.A :=
  ((TildePullback.tildePullbackIso f).app _).symm ≪≫
    (Scheme.Modules.pullback (Spec.map f)).mapIso (invariantTildeIso f D) ≪≫
      invariantPullbackIso f D hf

/-- Over a noetherian affine base, the invariant sheaf of an actual geometric
line-bundle coaction is a line bundle. -/
theorem invariantSheaf_isLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat)
    (hD : Line.Bundles.IsLine D.A) :
    Line.Bundles.IsLine (BeckDescent.invariantSheaf (Spec.map f) D) := by
  have : D.A.IsQuasicoherent := QuasiCoherent.isQuasicoherent_of_isLine D.A hD
  let M := (moduleSpecΓFunctor (R := R)).obj
    (BeckDescent.invariantSheaf (Spec.map f) D)
  have hExt : Module.Invertible S ((ModuleCat.extendScalars f.hom).obj M) :=
    Classification.invertible_of_isLine_tilde _
      (hD.of_iso (extendedInvariantTildeIso f D hf.flat).symm)
  let : Algebra R S := f.hom.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  have : Module.Invertible S (S ⊗[R] M) := hExt
  have : Module.Invertible R M :=
    LineDescent.invertible_of_faithfullyFlat_baseChange_noetherian R S M
  exact (TildePullback.isLine_tilde_of_invertible M).of_iso (invariantTildeIso f D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Invariant
