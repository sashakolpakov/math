import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

/-! # Scaled Line Isomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledLineIsomorphisms

noncomputable section

/-! Correct actual line isomorphisms by regular units and remove their composition defect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

variable {X Y : Scheme.{u}} {M N P : X.Modules}

/-- Rescale an actual isomorphism by a unit of the base scheme. -/
def rescale (e : M ≅ N) (r : Γ(X, ⊤)ˣ) : M ≅ N := Isogenies.NeighborCounting.ModuleScalar.scalarIso M r ≪≫ e

theorem rescale_one (e : M ≅ N) : rescale e 1 = e := by
  apply Iso.ext
  change Isogenies.NeighborCounting.ModuleScalar.scalarEnd M 1 ≫ e.hom = e.hom
  rw [Isogenies.NeighborCounting.ModuleScalar.scalarEnd_one, Category.id_comp]

theorem rescale_postcomp (e : M ≅ N) (f : N ≅ P) (r : Γ(X, ⊤)ˣ) :
    rescale (e ≪≫ f) r = rescale e r ≪≫ f := (Iso.trans_assoc _ _ _).symm

theorem rescale_precomp (e : M ≅ N) (f : N ≅ P) (r : Γ(X, ⊤)ˣ) :
    rescale (e ≪≫ f) r = e ≪≫ rescale f r := by
  apply Iso.ext
  change Isogenies.NeighborCounting.ModuleScalar.scalarEnd M r.val ≫ e.hom ≫ f.hom = e.hom ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd N r.val ≫ f.hom
  simpa only [Category.assoc] using congrArg (fun m => m ≫ f.hom) (Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality e.hom r.val)

theorem rescale_rescale (e : M ≅ N) (r s : Γ(X, ⊤)ˣ) :
    rescale (rescale e r) s = rescale e (s * r) := by
  apply Iso.ext
  change Isogenies.NeighborCounting.ModuleScalar.scalarEnd M s.val ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd M r.val ≫ e.hom = Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (s.val * r.val) ≫ e.hom
  rw [Isogenies.NeighborCounting.ModuleScalar.scalarEnd_mul, Category.assoc]

theorem rescale_trans (e : M ≅ N) (f : N ≅ P) (r s : Γ(X, ⊤)ˣ) :
    rescale e r ≪≫ rescale f s = rescale (e ≪≫ f) (r * s) := by
  apply Iso.ext
  change (Isogenies.NeighborCounting.ModuleScalar.scalarEnd M r.val ≫ e.hom) ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd N s.val ≫ f.hom =
    Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (r.val * s.val) ≫ e.hom ≫ f.hom
  rw [Isogenies.NeighborCounting.ModuleScalar.scalarEnd_mul]
  simpa only [Category.assoc] using
    congrArg (fun m => Isogenies.NeighborCounting.ModuleScalar.scalarEnd M r.val ≫ m ≫ f.hom) (Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality e.hom s.val).symm

theorem rescale_pullback (a : Y ⟶ X) (e : M ≅ N) (r : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pullback a).mapIso (rescale e r) =
      rescale ((Scheme.Modules.pullback a).mapIso e) (Units.map a.appTop.hom r) := by
  apply Iso.ext
  change (Scheme.Modules.pullback a).map (Isogenies.NeighborCounting.ModuleScalar.scalarEnd M r.val ≫ e.hom) =
    Isogenies.NeighborCounting.ModuleScalar.scalarEnd ((Scheme.Modules.pullback a).obj M) (a.appTop r.val) ≫
      (Scheme.Modules.pullback a).map e.hom
  rw [Functor.map_comp, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback]

/-- A solution of the unit-valued defect equation makes the corrected transports compose exactly. -/
theorem corrected_comp (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (e : M ≅ N) (f : N ≅ P) (g : M ≅ P)
    (r s v : Γ(X, ⊤)ˣ) (h : Line.IsoRatios.ratio hM (e ≪≫ f) g * v = r * s) :
    rescale e r⁻¹ ≪≫ rescale f s⁻¹ = rescale g v⁻¹ := by
  have hg : e ≪≫ f = rescale g (Line.IsoRatios.ratio hM (e ≪≫ f) g) := by
    apply Iso.ext
    exact (Line.IsoRatios.ratio_spec hM (e ≪≫ f) g).symm
  have hc : (r⁻¹ * s⁻¹) * Line.IsoRatios.ratio hM (e ≪≫ f) g = v⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    calc
      ((r⁻¹ * s⁻¹) * Line.IsoRatios.ratio hM (e ≪≫ f) g) * v =
          (r⁻¹ * s⁻¹) * (Line.IsoRatios.ratio hM (e ≪≫ f) g * v) := by ac_rfl
      _ = (r⁻¹ * s⁻¹) * (r * s) := congrArg (fun z => (r⁻¹ * s⁻¹) * z) h
      _ = 1 := by rw [mul_mul_mul_comm, inv_mul_cancel, inv_mul_cancel, mul_one]
  rw [rescale_trans, hg, rescale_rescale, hc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledLineIsomorphisms
