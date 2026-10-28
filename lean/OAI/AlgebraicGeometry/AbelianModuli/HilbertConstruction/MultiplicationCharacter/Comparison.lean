import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TorsorStructureComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageIntertwining
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAveragePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.CharacterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandIntertwining

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual multiplication-torsor comparison intertwines character projectors and therefore gives actual maps from pulled-back multiplication-character sheaves to constant-torsor character sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

theorem Abelian.Schemes.AbelianScheme.multiplication_schemeCoefficientMap :
    (A.multiplication N).left.appTop.hom.comp (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) =
      Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom := by
  calc
    (A.multiplication N).left.appTop.hom.comp (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) =
        Coefficient.ModulePresheaf.schemeCoefficientMap ((A.multiplication N).left ≫ A.scheme.hom) := by
      ext r
      rfl
    _ = _ := congrArg Coefficient.ModulePresheaf.schemeCoefficientMap (A.multiplication N).w

variable [NeZero N]

theorem Abelian.Schemes.AbelianScheme.fullLevelStructureComparison_projector
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) :
    (Scheme.Modules.pullback (A.multiplication N).left).map
        (A.fullLevelMultiplicationProjector (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ) ≫
      A.fullLevelStructureComparison level =
    A.fullLevelStructureComparison level ≫
      Sheaf.CharacterAverages.sheafCharacterAverage (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom)
        (Constant.StructureRepresentation.constantStructurePushforward A.scheme.left _)
        (Constant.StructureRepresentation.constantStructureRepresentation A.scheme.left _) χ := by
  let F := Scheme.Modules.pullback (A.multiplication N).left
  let M := A.multiplicationStructurePushforward N
  let ρ := (F.mapEnd M).comp (A.fullLevelStructureRepresentation level)
  let σ := Constant.StructureRepresentation.constantStructureRepresentation A.scheme.left
    (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)))
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom
  let φ := A.fullLevelStructureComparison level
  have hp : F.map (A.fullLevelMultiplicationProjector c level χ) =
      Sheaf.CharacterAverages.sheafCharacterAverage c (F.obj M) ρ χ :=
    (Sheaf.CharacterAveragePullback.sheafCharacterAverage_pullback (A.multiplication N).left c M
      (A.fullLevelStructureRepresentation level) χ).trans
      (congrArg (fun d => Sheaf.CharacterAverages.sheafCharacterAverage d (F.obj M) ρ χ)
        (A.multiplication_schemeCoefficientMap (N := N)))
  exact (congrArg (fun z => z ≫ φ) hp).trans
    (Sheaf.CharacterAverageIntertwining.sheafCharacterAverage_intertwines c ρ σ φ
      (fun a => A.fullLevelStructureComparison_intertwines level a) χ)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterComparison
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (Scheme.Modules.pullback (A.multiplication N).left).obj
        (A.multiplicationCharacterSheaf level χ) ⟶
      Constant.CharacterSheafSections.constantCharacterSheaf (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom)
        (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) χ :=
  (A.multiplicationCharacterPullbackIso level (A.multiplication N).left χ hN).hom ≫
    Sheaf.SummandIntertwining.sheafSummandIntertwiningMap _ _ (A.fullLevelStructureComparison level)
      (A.fullLevelStructureComparison_projector level χ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
