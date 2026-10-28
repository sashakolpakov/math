import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension

/-! # Open Group Chart Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenGroupChartDimension.Construction

noncomputable section

/-! Every nonempty affine open in the geometric group has its full Krull dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

theorem topologicalKrullDim_openImmersion_le
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim,
    GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  rw [← coheight_eq_of_isOpenImmersion f (x := x)]
  exact Order.coheight_le_krullDim (f x)

theorem topologicalKrullDim_openImmersion_eq_of_transitive_closedPoints
    {X Y : Scheme} [Nonempty X] [JacobsonSpace X] [JacobsonSpace Y]
    (f : X ⟶ Y) [IsOpenImmersion f]
    (htrans : ∀ (x y : Y), IsClosed {x} → IsClosed {y} →
      ∃ α : Y ≅ Y, α.hom x = y) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm (topologicalKrullDim_openImmersion_le f)
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := X) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hfx : IsClosed {f x} := by
    change x ∈ f ⁻¹' closedPoints Y
    rw [f.isOpenEmbedding.preimage_closedPoints]
    exact hx
  rw [GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints Y htrans (f x) hfx,
    ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion f (x := x),
    GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim]
  exact Order.coheight_le_krullDim x

universe u

theorem group_affine_chart_krullDimension
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (U : A.left.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ringKrullDim Γ(A.left, U) = topologicalKrullDim A.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : JacobsonSpace (Spec Γ(A.left, U)) :=
    LocallyOfFiniteType.jacobsonSpace (hU.fromSpec ≫ A.hom)
  have : Nonempty (Spec Γ(A.left, U)) :=
    hU.isoSpec.inv.homeomorph.toEquiv.nonempty
  have he := topologicalKrullDim_openImmersion_eq_of_transitive_closedPoints hU.fromSpec
    (fun x y hx hy => by
      obtain ⟨α, _, hxy, _⟩ := FlatTranslations.Construction.multiplication_transitive_automorphisms A 1 x y hx hy
      exact ⟨α, hxy⟩)
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(A.left, U)).symm.trans he

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenGroupChartDimension.Construction
