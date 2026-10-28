import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Topology.KrullDimension

/-! # Group Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction

noncomputable section

/-! The dimension of an algebraic group through its local ring at a closed point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The topological Krull dimension of a scheme is the Krull dimension
of its specialization order. -/
theorem topologicalKrullDim_eq_specialization_krullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

/-- If automorphisms are transitive on closed points of a Jacobson scheme,
its dimension equals the dimension of the local ring at any closed point. -/
theorem topologicalKrullDim_eq_stalk_of_transitive_closedPoints
    (X : Scheme) [JacobsonSpace X]
    (htrans : ∀ (x y : X), IsClosed {x} → IsClosed {y} →
      ∃ α : X ≅ X, α.hom x = y)
    (x : X) (hx : IsClosed {x}) :
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_eq_coheight, topologicalKrullDim_eq_specialization_krullDim]
  apply le_antisymm
  · rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro z
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
      (Z := closure ({z} : Set X)) (Set.singleton_nonempty z).closure
      isClosed_closure.isLocallyClosed
    have hyz : y ≤ z := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
    obtain ⟨α, hα⟩ := htrans y x hyc hx
    have hdim : Order.coheight y = Order.coheight x := by
      rw [← hα]
      exact (coheight_eq_of_isOpenImmersion α.hom).symm
    exact WithBot.coe_le_coe.mpr ((Order.coheight_anti hyz).trans_eq hdim)
  · exact Order.coheight_le_krullDim x

/-- A locally Noetherian Jacobson scheme with transitive closed points
has a finite natural-number dimension. -/
theorem exists_nat_dimension_of_transitive_closedPoints
    (X : Scheme) [IsLocallyNoetherian X] [JacobsonSpace X] [Nonempty X]
    (htrans : ∀ (x y : X), IsClosed {x} → IsClosed {y} →
      ∃ α : X ≅ X, α.hom x = y) :
    ∃ g : ℕ, topologicalKrullDim X = (g : WithBot ℕ∞) := by
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := X) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hdim := topologicalKrullDim_eq_stalk_of_transitive_closedPoints X htrans x hx
  have hfin : (Order.coheight x : WithBot ℕ∞) < ⊤ := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_lt_top
  have hne : Order.coheight x ≠ ⊤ := by
    intro h
    simp only [h, WithBot.coe_top, lt_self_iff_false] at hfin
  refine ⟨(Order.coheight x).toNat, ?_⟩
  rw [hdim, ringKrullDim_stalk_eq_coheight]
  exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (ENat.natCast_toNat hne).symm

/-- A smooth proper geometrically connected commutative group over an
algebraically closed field has finite topological Krull dimension. -/
theorem exists_nat_dimension_group_over_algClosed
    {K : Type*} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    ∃ g : ℕ, topologicalKrullDim A.left = (g : WithBot ℕ∞) := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  exact exists_nat_dimension_of_transitive_closedPoints A.left (fun x y hx hy => by
    obtain ⟨α, _, hxy, _⟩ := FlatTranslations.Construction.multiplication_transitive_automorphisms A 1 x y hx hy
    exact ⟨α, hxy⟩)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction
