import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Isogeny Pair Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyPairComparison

noncomputable section

/-! Isomorphisms of both abelian schemes identify an isogeny's actual
kernel groups and finite-flat polarization type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A D A' D' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A' D')
    (eA : A.scheme ≅ A'.scheme) (eD : D.scheme ≅ D'.scheme)
    [IsMonHom eA.hom] [IsMonHom eD.hom]
    (he : p.hom ≫ eD.hom = eA.hom ≫ q.hom)

def isogenyKernelComparison (T : Over S) : p.kernelAt T ≃* q.kernelAt T where
  toFun x := ⟨x.val ≫ eA.hom, by
    have hx : x.val ≫ p.hom = 1 := MonoidHom.mem_ker.mp x.property
    change (x.val ≫ eA.hom) ≫ q.hom = 1
    rw [Category.assoc, ← he, ← Category.assoc, hx, MonObj.one_comp]⟩
  invFun x := ⟨x.val ≫ eA.inv, by
    have hx : x.val ≫ q.hom = 1 := MonoidHom.mem_ker.mp x.property
    change (x.val ≫ eA.inv) ≫ p.hom = 1
    apply (cancel_mono eD.hom).mp
    simp only [Category.assoc, he, eA.inv_hom_id_assoc, hx, MonObj.one_comp]⟩
  left_inv x := Subtype.ext (by simp only [Category.assoc, eA.hom_inv_id, Category.comp_id])
  right_inv x := Subtype.ext (by simp only [Category.assoc, eA.inv_hom_id, Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val eA.hom)

include he in
theorem isogenyPolarizationType_of_pairComparison {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) : q.HasPolarizationType δ := by
  have : IsIso eA.hom.left := inferInstanceAs (IsIso (((Over.forget S).mapIso eA).hom))
  have : IsIso eD.hom.left := inferInstanceAs (IsIso (((Over.forget S).mapIso eD).hom))
  have hc : IsPullback eA.hom.left p.hom.left q.hom.left eD.hom.left :=
    IsPullback.of_horiz_isIso ⟨congrArg Over.Hom.left he.symm⟩
  refine ⟨?_, ?_⟩
  · intro d'
    obtain ⟨d, rfl⟩ := eD.hom.left.surjective d'
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hc d).symm.trans (hp.degree d)
  · intro K _ _ s
    exact ⟨(isogenyKernelComparison p q eA eD he (Over.mk s)).symm.trans
      (hp.geometricKernel K s).some⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyPairComparison
