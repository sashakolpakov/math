import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedFinitePoints
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsogenyComparisonKernel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Algebraically Closed Kernel Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedKernelType.Construction

noncomputable section

/-! Geometric kernel groups of an isogeny over an algebraically closed
field do not change under field extension. Both the finite-flat degree
and all geometric elementary divisors descend from one such extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

def algebraicallyClosedFinitePointsMulEquiv
    {k K : Type} [Field k] [IsAlgClosed k] [Field K]
    (X : Over (Spec (.of k))) [GrpObj X] [IsFinite X.hom]
    (u : Spec (.of K) ⟶ Spec (.of k)) :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ X) ≃* (Over.mk u ⟶ X) :=
  MulEquiv.ofBijective ({
    toFun r := (Over.homMk u (Category.comp_id u) : Over.mk u ⟶ Over.mk (𝟙 _)) ≫ r
    map_mul' r s := MonObj.comp_mul _ r s } :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ X) →ₙ* (Over.mk u ⟶ X))
    (AlgebraicallyClosedFinitePoints.Construction.algebraicallyClosed_quasiFinite_points_bijective X u)

set_option backward.isDefEq.respectTransparency false in
def algebraicallyClosedIsogenyKernelFieldEquiv
    {k K : Type} [Field k] [IsAlgClosed k] [Field K]
    {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (u : Spec (.of K) ⟶ Spec (.of k)) :
    p.kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃* p.kernelAt (Over.mk u) := by
  let : GrpObj (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) := Picard.PoincareBundle.Kernel.Scheme.kernelGroup p.hom
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite p.hom
  exact (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv p.hom (Over.mk (𝟙 (Spec (.of k))))).symm.trans
    ((algebraicallyClosedFinitePointsMulEquiv (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) u).trans
      (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv p.hom (Over.mk u)))

set_option backward.isDefEq.respectTransparency false in
theorem isogeny_type_of_algebraicallyClosed_field_pullback
    {k L : Type} [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L]
    {g : ℕ} {δ : Fin g → ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (u : Spec (.of L) ⟶ Spec (.of k))
    (hp : (p.pullback u).HasPolarizationType δ) : p.HasPolarizationType δ := by
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨z, rfl⟩ := (CategoryTheory.Limits.pullback.fst B.scheme.hom u).surjective y
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ (PELModuli.IntegralModel.Specialization.base_change_square u p.hom) z).symm.trans
      (hp.degree z)
  · intro K _ _ s
    have he : Nonempty (p.kernelAt (Over.mk u) ≃*
        Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) := by
      have h : Nonempty (p.kernelAt (Over.mk (𝟙 (Spec (.of L)) ≫ u)) ≃*
          Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) :=
          ⟨(p.kernelBaseChangeEquiv u (Over.mk (𝟙 (Spec (.of L))))).symm.trans
            (hp.geometricKernel L (𝟙 (Spec (.of L)))).some⟩
      exact (congrArg (fun v : Spec (.of L) ⟶ Spec (.of k) =>
        Nonempty (p.kernelAt (Over.mk v) ≃*
          Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))))
        (Category.id_comp u)).mp h
    exact ⟨(algebraicallyClosedIsogenyKernelFieldEquiv p s).symm.trans
      ((algebraicallyClosedIsogenyKernelFieldEquiv p u).trans he.some)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedKernelType.Construction
