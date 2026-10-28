import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandIntertwining

/-! # Comparison Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.ComparisonTransport

noncomputable section

/-! Two actual intertwining comparisons transport an endomorphism-compatible pullback isomorphism back to the original sheaf. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules) {M P : X.Modules}

def sheafComparisonTransport (e : M ≅ P) (d : F.obj P ≅ P) : F.obj M ≅ M :=
  F.mapIso e ≪≫ d ≪≫ e.symm

theorem sheafComparisonTransport_intertwines (e : M ≅ P) (d : F.obj P ≅ P)
    (p : End M) (q : End P) (he : p ≫ e.hom = e.hom ≫ q)
    (hd : F.map q ≫ d.hom = d.hom ≫ q) :
    F.map p ≫ (sheafComparisonTransport F e d).hom =
      (sheafComparisonTransport F e d).hom ≫ p := by
  have hF : F.map p ≫ F.map e.hom = F.map e.hom ≫ F.map q := by
    rw [← F.map_comp, ← F.map_comp, he]
  calc
    F.map p ≫ (sheafComparisonTransport F e d).hom =
        (F.map p ≫ F.map e.hom) ≫ d.hom ≫ e.inv := by
      simp only [sheafComparisonTransport, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Category.assoc]
    _ = (F.map e.hom ≫ F.map q) ≫ d.hom ≫ e.inv :=
      congrArg (fun z => z ≫ d.hom ≫ e.inv) hF
    _ = F.map e.hom ≫ d.hom ≫ q ≫ e.inv := by
      simpa only [Category.assoc] using congrArg (fun z => F.map e.hom ≫ z ≫ e.inv) hd
    _ = F.map e.hom ≫ d.hom ≫ e.inv ≫ p := by
      rw [SummandIntertwining.sheafProjector_intertwining_inverse p q e he]
    _ = (sheafComparisonTransport F e d).hom ≫ p := by
      simp only [sheafComparisonTransport, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.ComparisonTransport
