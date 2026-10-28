import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.GeometricRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PureTorsionRigidity

/-! # Pullback Torsion Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackTorsionRigidity

noncomputable section

/-! A prescribed full level at least three forces automorphisms of
every pullback of a finite-type pure family to fix every finite torsion
scheme. The pullback base may be arbitrary and nonreduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [CharZero K] [Countable K]
    {X S : Scheme.{0}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N L : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X)

include p in
theorem purePullback_geometric_abelian_eq_id (hN : 3 ≤ N) (t : S ⟶ X)
    {k : Type} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ S)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback t).pullback x) ((A.pullback t).pullback x)) :
    e.abelian.hom = 𝟙 ((A.abelian.pullback t).pullback x).scheme :=
  AutomorphismDescent.pure_abelian_eq_id_via e (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A t x)
    (fun j => GeometricRigidity.pureGeometricPullback_abelian_eq_id p A hN (x ≫ t) j)

include p in
theorem purePullback_automorphism_torsion_eq_id [NeZero L]
    (hN : 3 ≤ N) (t : S ⟶ X)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (A.pullback t)) :
    HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap L e.abelian.hom =
      𝟙 ((A.abelian.pullback t).torsionScheme L) := by
  let B := (A.pullback t).abelian
  let : Etale (B.torsionScheme L).hom := (TorsionEtaleAt.TorsionEtale.torsion_finite_etale B (t ≫ p) L).2
  apply (TorsionGeometricDetection.torsionMap_eq_of_geometric_pullbacks B B e.abelian.hom (𝟙 B.scheme) ?_).trans
    (HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap_id B L)
  intro k hk hclosed x
  exact (purePullback_geometric_abelian_eq_id p A hN t x (e.pullback x)).trans
    ((Over.pullback x).map_id B.scheme).symm

include p in
theorem purePullback_automorphism_preserves_level [NeZero L]
    (hN : 3 ≤ N) (t : S ⟶ X)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (A.pullback t))
    (β : (A.abelian.pullback t).FullLevel L) : Level.Stabilizers.LevelCover.PreservesFullLevel β e.abelian.hom :=
  PureTorsionRigidity.preserves_level_of_torsionMap_eq_id (A.pullback t).abelian e.abelian.hom
    (purePullback_automorphism_torsion_eq_id p A hN t e) β

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackTorsionRigidity
