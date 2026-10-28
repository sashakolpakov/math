import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Embedding -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding

noncomputable section

/-!
# Native crystalline sites along open immersions

Composing the actual residual open immersion embeds the crystalline
site of an open subscheme fully faithfully into the original site.
Ambient PD rings and their section maps are preserved literally.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

def object (Q : Site.Object p k X) : Site.Object p k Y where
  residueRing := Q.residueRing
  thickening := Q.thickening
  immersion := Q.immersion ≫ j.left
  over_base := by rw [Category.assoc, j.w, Q.over_base]

def map {P Q : Site.Object p k X} (f : P ⟶ Q) : object p k j P ⟶ object p k j Q where
  reducedMap := f.reducedMap
  ambientMap := f.ambientMap
  reduction_comm := f.reduction_comm
  dp_comp := f.dp_comp
  over_X := by
    change Spec.map (CommRingCat.ofHom f.reducedMap.toRingHom) ≫ (Q.immersion ≫ j.left) =
      P.immersion ≫ j.left
    rw [← Category.assoc, f.over_X]

def functor : Site.Object p k X ⥤ Site.Object p k Y where
  obj := object p k j
  map := CrystallineOpenEmbedding.map p k j
  map_id _ := Site.Object.Hom.ext _ _ rfl rfl
  map_comp _ _ := Site.Object.Hom.ext _ _ rfl rfl

def preimage {P Q : Site.Object p k X}
    (f : (functor p k j).obj P ⟶ (functor p k j).obj Q) : P ⟶ Q where
  reducedMap := f.reducedMap
  ambientMap := f.ambientMap
  reduction_comm := f.reduction_comm
  dp_comp := f.dp_comp
  over_X := by
    apply (cancel_mono j.left).mp
    exact (Category.assoc _ _ _).trans f.over_X

def fullyFaithful : (functor p k j).FullyFaithful where
  preimage := CrystallineOpenEmbedding.preimage p k j
  map_preimage _ := Site.Object.Hom.ext _ _ rfl rfl
  preimage_map _ := Site.Object.Hom.ext _ _ rfl rfl

def ambientIso : functor p k j ⋙ Site.ambient p k Y ≅ Site.ambient p k X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

def functionsIso : (functor p k j).op ⋙ Site.functions p k Y ≅ Site.functions p k X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding
