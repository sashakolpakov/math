import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Etale Source Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleSourceMonomorphism.Construction

/-! Geometric injectivity proves a monomorphism when the source is
etale over the base. Arbitrary nonreduced test schemes are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem etaleSource_mono_of_geometric_injective
    {S : Scheme.{u}} {H G : Over S} [Etale H.hom] (i : H ⟶ G)
    (hi : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      Function.Injective (fun x : Over.mk s ⟶ H => x ≫ i)) : Mono i := by
  constructor
  intro T x y hxy
  apply Geometric.Points.Construction.etale_ext_of_geometric_points x y
  intro k _ _ s z
  apply hi k s
  exact (Category.assoc z x i).trans ((congrArg (fun a => z ≫ a) hxy).trans (Category.assoc z y i).symm)

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleSourceMonomorphism.Construction
