import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.OpenLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens

/-! # Principal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Principal.CrystallineOpenPrincipal

noncomputable section

/-!
# Principal opens commute with the native open-site inclusion

The actual localized PD rings agree, so the comparison preserves both
ring maps literally and commutes with the principal-open projections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]
  (Q : Site.Object p k X) (s : Q.thickening.ring)

def map : (Embedding.CrystallineOpenEmbedding.functor p k j).obj
    (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s) ⟶
      CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k Y ((Embedding.CrystallineOpenEmbedding.functor p k j).obj Q) s where
  reducedMap := AlgHom.id k _
  ambientMap := AlgHom.id (WittVector p k) _
  reduction_comm := fun _ => rfl
  dp_comp := (DividedPowers.DPMorphism.id
    (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s).thickening.dividedPowers).isDPMorphism
  over_X := by
    change Spec.map (𝟙 (CommRingCat.of (Localization.Away (Q.thickening.reduction s)))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Q.residueRing
        (Localization.Away (Q.thickening.reduction s)))) ≫ (Q.immersion ≫ j.left)) =
      (Spec.map (CommRingCat.ofHom (algebraMap Q.residueRing
        (Localization.Away (Q.thickening.reduction s)))) ≫ Q.immersion) ≫ j.left
    rw [Spec.map_id, Category.id_comp, Category.assoc]

theorem projection : CrystallineOpenPrincipal.map p k j Q s ≫
    CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k Y ((Embedding.CrystallineOpenEmbedding.functor p k j).obj Q) s =
      (Embedding.CrystallineOpenEmbedding.functor p k j).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s) :=
  Site.Object.Hom.ext _ _ rfl rfl

instance image_open : IsOpenImmersion ((Site.ambient p k Y).map
    ((Embedding.CrystallineOpenEmbedding.functor p k j).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))) := by
  change IsOpenImmersion ((Site.ambient p k X).map
    (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Principal.CrystallineOpenPrincipal
