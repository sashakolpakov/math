import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.TranslationStructureComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.CharacterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAveragePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageIntertwining
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward

/-! # Character Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over every test scheme, the actual pulled-back multiplication-character sheaves are isomorphic to their translates by N-fold points. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {K : Type u} [Field K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.familyCharacterProjector (T : Over (Spec (.of K)))
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) :
    End ((Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationStructurePushforward N)) :=
  (Scheme.Modules.pullback (snd T A.scheme).left).map
    (A.fullLevelMultiplicationProjector (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ)

theorem Abelian.Schemes.AbelianScheme.familyCharacterProjector_idempotent (T : Over (Spec (.of K)))
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    A.familyCharacterProjector level T χ ≫ A.familyCharacterProjector level T χ =
      A.familyCharacterProjector level T χ := by
  unfold Abelian.Schemes.AbelianScheme.familyCharacterProjector
  rw [← Functor.map_comp, A.fullLevelMultiplicationProjector_idempotent
    (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ hN]

theorem Abelian.Schemes.AbelianScheme.familyTranslationComparisonIso_projector {T : Over (Spec (.of K))} (a : T ⟶ A.scheme)
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).map
      (A.familyCharacterProjector level T χ) ≫ (A.familyTranslationComparisonIso level a).hom =
    (A.familyTranslationComparisonIso level a).hom ≫ A.familyCharacterProjector level T χ := by
  let r := (snd T A.scheme).left
  let t := (A.translation (a ^ N)).left
  let P := Scheme.Modules.pullback r
  let F := Scheme.Modules.pullback t
  let M := A.multiplicationStructurePushforward N
  let ρ := (P.mapEnd M).comp (A.fullLevelStructureRepresentation level)
  let σ := (F.mapEnd (P.obj M)).comp ρ
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom
  let cT := r.appTop.hom.comp c
  let φ := (A.familyTranslationComparisonIso level a).hom
  have hc : cT = Coefficient.ModulePresheaf.schemeCoefficientMap (T ⊗ A.scheme).hom :=
    (Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp r A.scheme.hom).symm.trans
      (congrArg Coefficient.ModulePresheaf.schemeCoefficientMap (snd T A.scheme).w)
  have ht : t.appTop.hom.comp cT = cT := by
    rw [hc, ← Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp]
    exact congrArg Coefficient.ModulePresheaf.schemeCoefficientMap (A.translation (a ^ N)).w
  have hP : A.familyCharacterProjector level T χ =
      Sheaf.CharacterAverages.sheafCharacterAverage cT (P.obj M) ρ χ :=
    Sheaf.CharacterAveragePullback.sheafCharacterAverage_pullback r c M (A.fullLevelStructureRepresentation level) χ
  have hFP : F.map (A.familyCharacterProjector level T χ) =
      Sheaf.CharacterAverages.sheafCharacterAverage cT (F.obj (P.obj M)) σ χ :=
    (congrArg (fun p : End (P.obj M) => F.map p) hP).trans
      ((Sheaf.CharacterAveragePullback.sheafCharacterAverage_pullback t cT (P.obj M) ρ χ).trans
        (congrArg (fun d => Sheaf.CharacterAverages.sheafCharacterAverage d (F.obj (P.obj M)) σ χ) ht))
  exact (congrArg (fun p => p ≫ φ) hFP).trans
    ((Sheaf.CharacterAverageIntertwining.sheafCharacterAverage_intertwines cT σ ρ φ
      (fun i => A.familyTranslationComparisonIso_intertwines level a i) χ).trans
        (congrArg (fun p => φ ≫ p) hP.symm))

def Abelian.Schemes.AbelianScheme.familyCharacterTranslationIso {T : Over (Spec (.of K))} (a : T ⟶ A.scheme)
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).obj
      ((Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationCharacterSheaf level χ)) ≅
    (Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationCharacterSheaf level χ) := by
  let r := (snd T A.scheme).left
  let t := (A.translation (a ^ N)).left
  let F := Scheme.Modules.pullback t
  let q := A.familyCharacterProjector level T χ
  let e : (Scheme.Modules.pullback r).obj (A.multiplicationCharacterSheaf level χ) ≅
      IdempotentSheafSummands.idempotentSheafSummand q := A.multiplicationCharacterPullbackIso level r χ hN
  exact F.mapIso e ≪≫
    Sheaf.SummandFunctoriality.sheafSummandPullbackIso t q (A.familyCharacterProjector_idempotent level T χ hN) ≪≫
      Sheaf.SummandIntertwining.sheafSummandIntertwiningIso (F.map q) q (A.familyTranslationComparisonIso level a)
        (A.familyTranslationComparisonIso_projector level a χ) ≪≫ e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
