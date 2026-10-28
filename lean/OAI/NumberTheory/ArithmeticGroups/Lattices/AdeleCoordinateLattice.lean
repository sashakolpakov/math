import OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete

/-! # Adele Coordinate Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdeleCoordinateLattice.Construction

noncomputable section

/-! Diagonal images of finite integral coordinate modules in the product
of all archimedean completions are discrete and closed. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

abbrev CoordinateAdeleSpace (k I : Type) [Field k] :=
  (v : InfinitePlace k) → I → v.Completion

def coordinateAdeleEmbedding (k I : Type) [Field k] :
    (I → k) →ₗ[ℤ] CoordinateAdeleSpace k I where
  toFun x v i := algebraMap k v.Completion (x i)
  map_add' x y := by funext v i; exact map_add (algebraMap k v.Completion) (x i) (y i)
  map_smul' z x := by
    funext v i
    exact map_zsmul (algebraMap k v.Completion).toAddMonoidHom z (x i)

def coordinateAdeleLattice {k I : Type} [Field k] [NumberField k]
    (Λ : Submodule (𝓞 k) (I → k)) : Submodule ℤ (CoordinateAdeleSpace k I) :=
  (Λ.restrictScalars ℤ).map (coordinateAdeleEmbedding k I)

theorem coordinateAdeleLattice_discrete
    {k I : Type} [Field k] [NumberField k] [Finite I]
    (Λ : Submodule (𝓞 k) (I → k)) (hΛ : Λ.FG) :
    DiscreteTopology (coordinateAdeleLattice Λ) := by
  let J : I → Submodule (𝓞 k) k := fun i => Λ.map (LinearMap.proj i)
  let : ∀ i, DiscreteTopology (IntegralLattice.Construction.scalarLatticeImage (J i)) :=
    fun i => IntegralLattice.Construction.scalarLatticeImage_discrete (J i) (hΛ.map (LinearMap.proj i))
  let f : coordinateAdeleLattice Λ → (i : I) → IntegralLattice.Construction.scalarLatticeImage (J i) := fun x i =>
    ⟨InfiniteAdeleRing.ringEquiv_mixedSpace k (fun v => x.val v i), by
      obtain ⟨a, ha, he⟩ := x.property
      refine ⟨a i, ⟨a, ha, rfl⟩, ?_⟩
      change mixedEmbedding k (a i) = InfiniteAdeleRing.ringEquiv_mixedSpace k
        (show InfiniteAdeleRing k from fun v => x.val v i)
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      apply congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace k)
      funext v
      exact congrArg (fun z : CoordinateAdeleSpace k I => z v i) he⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    apply Discrete.Construction.continuous_adele_to_mixed.comp
    apply continuous_pi
    intro v
    exact (continuous_apply i).comp ((continuous_apply v).comp continuous_subtype_val)
  · intro x y h
    apply Subtype.ext
    funext v i
    have hi := congrArg (fun z : (j : I) → IntegralLattice.Construction.scalarLatticeImage (J j) => (z i).val) h
    exact congrFun ((InfiniteAdeleRing.ringEquiv_mixedSpace k).injective hi) v

theorem coordinateAdeleLattice_closed
    {k I : Type} [Field k] [NumberField k] [Finite I]
    (Λ : Submodule (𝓞 k) (I → k)) (hΛ : Λ.FG) :
    IsClosed (coordinateAdeleLattice Λ : Set (CoordinateAdeleSpace k I)) := by
  let : DiscreteTopology (coordinateAdeleLattice Λ) := coordinateAdeleLattice_discrete Λ hΛ
  exact (coordinateAdeleLattice Λ).toAddSubgroup.isClosed_of_discreteTopology

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdeleCoordinateLattice.Construction
