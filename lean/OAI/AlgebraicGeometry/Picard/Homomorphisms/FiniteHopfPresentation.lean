import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite Hopf Presentation -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation

noncomputable section

/-! Extract finite Hopf coordinates from a native finite commutative group
scheme over a field. No coordinate presentation is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem cocomm_of_commutative_hopfSpec
    (k A : Type u) [Field k] [CommRing A] [Bialgebra k A]
    [IsCommMonObj ((Spec (.of A)).asOver (Spec (.of k)))] : Coalgebra.IsCocomm k A := by
  let f : WithConv (A →ₐ[k] A ⊗[k] A) := WithConv.toConv Algebra.TensorProduct.includeLeft
  let g : WithConv (A →ₐ[k] A ⊗[k] A) := WithConv.toConv Algebra.TensorProduct.includeRight
  have hfg : f * g = g * f := by
    apply (Spec.mapMulEquiv (R := k) (S := A) (T := A ⊗[k] A)).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hl : Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all ..) =
      AlgHom.id k (A ⊗[k] A) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro x y
    simp [f, g]
  have hr : Algebra.TensorProduct.lift g.ofConv f.ofConv (fun _ _ => .all ..) =
      (Algebra.TensorProduct.comm k A A).toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro x y
    simp [f, g]
  constructor
  apply LinearMap.ext
  intro x
  change TensorProduct.comm k A A (Coalgebra.comul x) = Coalgebra.comul x
  have h := congrArg (fun t : WithConv (A →ₐ[k] A ⊗[k] A) => t x) hfg
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, hl, hr] at h
  exact h.symm

theorem finite_commutative_hopfPresentation (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom] :
    ∃ A : CommHopfAlgCat k, Module.Finite k A ∧ Coalgebra.IsCocomm k A ∧
      Nonempty ((hopfSpec (.of k)).obj (op A) ≅ G) := by
  have hAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of k) (G := G)).mpr hAffine
  let i : ((hopfSpec (.of k)).obj A).X ≅ G.X := (Grp.forget _).mapIso e
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map i.hom))
  have hfinite : IsFinite ((hopfSpec (.of k)).obj A).X.hom := by
    rw [← i.hom.w]
    infer_instance
  have hf : Module.Finite k A.unop := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap k A.unop))).mp hfinite)
  have : IsMonHom i.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have hcomm : IsCommMonObj ((hopfSpec (.of k)).obj A).X := by
    apply (isCommMonObj_iff_isMulCommutative _).mpr
    intro T
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (cancel_mono i.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have : IsCommMonObj ((Spec (.of A.unop)).asOver (Spec (.of k))) := hcomm
  exact ⟨A.unop, hf, cocomm_of_commutative_hopfSpec k A.unop, ⟨e⟩⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
