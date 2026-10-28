import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Integral Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegralDimension.Dimension

noncomputable section

/-! Dimension invariance for integral surjective morphisms and algebraic field extensions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Specialization order computes the actual topological dimension of a scheme. -/
theorem topologicalKrullDim_eq_specialization_krullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

/-- An integral scheme over a field has closed points only. -/
theorem t1Space_of_integral_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsIntegralHom f] : T1Space X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let φ := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have : IsIntegralHom (Spec.map φ) := by
    dsimp [φ]
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.IsIntegral K Γ(X, ⊤) :=
    ⟨IsIntegralHom.SpecMap_iff.mp inferInstance⟩
  have : T1Space (Spec (.of Γ(X, ⊤))) := by
    constructor
    intro p
    apply p.isClosed_singleton_iff_isMaximal.mpr
    have : p.asIdeal.IsPrime := p.isPrime
    apply Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := K) p.asIdeal
    have : (p.asIdeal.comap (algebraMap K Γ(X, ⊤))).IsPrime := inferInstance
    simpa only [Ideal.eq_bot_of_prime] using (Ideal.bot_isMaximal :
      (⊥ : Ideal K).IsMaximal)
  exact X.isoSpec.inv.homeomorph.t1Space

/-- Fibers of an integral morphism are T1 spaces. -/
theorem t1Space_preimage_singleton_of_isIntegral
    {X Y : Scheme} (f : X ⟶ Y) [IsIntegralHom f] (y : Y) :
    T1Space (f ⁻¹' {y}) := by
  have : IsIntegralHom (f.fiberToSpecResidueField y) := by
    change IsIntegralHom (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  have : T1Space (f.fiber y) :=
    @t1Space_of_integral_over_field (Y.residueField y) _ _ (f.fiberToSpecResidueField y) ‹_›
  exact (f.fiberHomeo y).t1Space

/-- Integral morphisms do not identify distinct comparable points. -/
theorem strictMono_of_isIntegral
    {X Y : Scheme} (f : X ⟶ Y) [IsIntegralHom f] : StrictMono f := by
  intro x y hxy
  have hle : f x ≤ f y :=
    Scheme.le_iff_specializes.mpr ((Scheme.le_iff_specializes.mp hxy.le).map f.continuous)
  apply lt_iff_le_not_ge.mpr
  refine ⟨hle, ?_⟩
  intro hge
  have heq : f x = f y := ((Scheme.le_iff_specializes.mp hge).antisymm
    (Scheme.le_iff_specializes.mp hle)).eq
  have : T1Space (f ⁻¹' {f x}) := t1Space_preimage_singleton_of_isIntegral f (f x)
  have hspec : (⟨y, heq.symm⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ :=
    Topology.IsEmbedding.subtypeVal.specializes_iff.mp
      (Scheme.le_iff_specializes.mp hxy.le)
  have hxy' : y = x := congrArg Subtype.val hspec.eq
  exact hxy.not_ge (le_of_eq hxy')

/-- Integral morphisms preserve specialization heights, by incomparability
and lifting of specializations along their closed underlying maps. -/
theorem height_eq_of_isIntegral
    {X Y : Scheme} (f : X ⟶ Y) [IsIntegralHom f] (x : X) :
    Order.height x = Order.height (f x) := by
  apply Order.height_eq_of_strictMono f (strictMono_of_isIntegral f)
  intro a b hba
  obtain ⟨a', haa', ha'⟩ := f.isClosedMap.specializingMap
    (Scheme.le_iff_specializes.mp hba.le)
  refine ⟨a', lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr haa', ?_⟩, ha'⟩
  intro hge
  have : f a ≤ b := ha' ▸ Scheme.le_iff_specializes.mpr
    ((Scheme.le_iff_specializes.mp hge).map f.continuous)
  exact hba.not_ge this

/-- Integral surjective scheme morphisms preserve topological Krull dimension. -/
theorem topologicalKrullDim_eq_of_integral_surjective
    {X Y : Scheme} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_specialization_krullDim,
    topologicalKrullDim_eq_specialization_krullDim,
    Order.krullDim_eq_iSup_height, Order.krullDim_eq_iSup_height]
  simp_rw [height_eq_of_isIntegral f]
  exact (f.surjective.iSup_comp (fun y : Y => (Order.height y : WithBot ℕ∞)))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegralDimension.Dimension
