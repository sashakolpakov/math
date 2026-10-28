import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedPD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site

/-! # Opens -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens.CrystallinePrincipalOpens

noncomputable section

/-!
# Actual principal-open objects of the native crystalline site

Every principal open in the ambient ring of a native crystalline object
has a constructed object of the same site. Its residue immersion, reduction,
Witt algebra structure, and divided powers come from the actual localizations.
The canonical map to the original object is a native crystalline morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X) (s : Q.thickening.ring)

def object : Site.Object p k X where
  residueRing := CommRingCat.of (Localization.Away (Q.thickening.reduction s))
  thickening := LocalizedPD.LocalizedPDThickening.thickening p k Q.residueRing Q.thickening s
  immersion := Spec.map (CommRingCat.ofHom (algebraMap Q.residueRing
    (Localization.Away (Q.thickening.reduction s)))) ≫ Q.immersion
  over_base := by
    rw [Category.assoc, Q.over_base, ← Spec.map_comp]
    congr 1

def projection : object p k X Q s ⟶ Q where
  reducedMap := LocalizedPD.LocalizedPDThickening.reducedMap p k Q.residueRing Q.thickening s
  ambientMap := LocalizedPD.LocalizedPDThickening.ambientMap p k Q.residueRing Q.thickening s
  reduction_comm := LocalizedPD.LocalizedPDThickening.reduction_comm p k Q.residueRing Q.thickening s
  over_X := rfl
  dp_comp := LocalizedPD.LocalizedPDThickening.coefficients_isDPMorphism p k Q.residueRing Q.thickening s

instance ambient_openImmersion : IsOpenImmersion ((Site.ambient p k X).map (projection p k X Q s)) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap Q.thickening.ring (Localization.Away s))))
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens.CrystallinePrincipalOpens
