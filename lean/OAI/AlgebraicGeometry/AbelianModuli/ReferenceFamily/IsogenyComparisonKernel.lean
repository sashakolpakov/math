import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Isogeny Comparison Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsogenyComparisonKernel

noncomputable section

section

/-! A commuting pair of native group isomorphisms identifies the
full kernel groups of two isogenies on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g h : ℕ} {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {D E : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D) (w : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B E)
    (eA : A.scheme ≅ B.scheme) (eD : D.scheme ≅ E.scheme)
    [IsMonHom eA.hom] [IsMonHom eD.hom]
    (hc : eA.hom ≫ w.hom = f.hom ≫ eD.hom)

def isogenyComparisonKernelEquiv (T : Over S) : f.kernelAt T ≃* w.kernelAt T where
  toFun x := ⟨x.val ≫ eA.hom, by
    have hx : x.val ≫ f.hom = 1 := MonoidHom.mem_ker.mp x.property
    change (x.val ≫ eA.hom) ≫ w.hom = 1
    rw [Category.assoc, hc, ← Category.assoc, hx, MonObj.one_comp]⟩
  invFun x := ⟨x.val ≫ eA.inv, by
    change (x.val ≫ eA.inv) ≫ f.hom = 1
    apply (cancel_mono eD.hom).mp
    rw [Category.assoc, Category.assoc, ← hc, Iso.inv_hom_id_assoc, MonObj.one_comp]
    exact MonoidHom.mem_ker.mp x.property⟩
  left_inv x := Subtype.ext (by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  right_inv x := Subtype.ext (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val eA.hom)

end

/-! Native source and target comparisons preserve the finite-flat
degree and the full geometric polarization-kernel type. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem isogeny_type_of_comparison
    {S : Scheme.{0}} {g : ℕ} {δ : Fin g → ℕ} {A B D E : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D) (w : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B E)
    (eA : A.scheme ≅ B.scheme) (eD : D.scheme ≅ E.scheme)
    [IsMonHom eA.hom] [IsMonHom eD.hom]
    (hc : eA.hom ≫ w.hom = f.hom ≫ eD.hom)
    (hf : f.HasPolarizationType δ) : w.HasPolarizationType δ where
  degree y := by
    have : IsIso eA.hom.left := inferInstanceAs (IsIso ((Over.forget S).map eA.hom))
    have : IsIso eD.hom.left := inferInstanceAs (IsIso ((Over.forget S).map eD.hom))
    have hp : IsPullback eA.hom.left f.hom.left w.hom.left eD.hom.left :=
      IsPullback.of_horiz_isIso ⟨congrArg Over.Hom.left hc⟩
    obtain ⟨x, rfl⟩ := eD.hom.left.surjective y
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp x).symm.trans (hf.degree x)
  geometricKernel K _ _ s :=
    ⟨(isogenyComparisonKernelEquiv f w eA eD hc (Over.mk s)).symm.trans
      (hf.geometricKernel K s).some⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsogenyComparisonKernel
