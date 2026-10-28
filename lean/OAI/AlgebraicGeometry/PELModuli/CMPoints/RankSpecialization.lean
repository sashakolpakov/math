import OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Rank Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RankSpecialization

noncomputable section

/-! Comparison of FiniteEtale's coordinate dimensions with the geometric ranks
of finite flat morphisms, and constancy under specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem finite_group_geometric_rank {k : Type} [Field k]
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) (x : Spec (.of k)) :
    H.scheme.hom.finrank x = Module.finrank k H.algebra := by
  exact (Scheme.Hom.finrank_SpecMap_algebraMap k H.algebra x).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := H.algebra)) x)

theorem finite_group_rank_of_iso {k : Type} [Field k]
    (G H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) (e : G.scheme ≅ H.scheme) :
    Module.finrank k G.algebra = Module.finrank k H.algebra := by
  let x : Spec (.of k) := IsLocalRing.closedPoint k
  have : IsIso e.hom.left := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of k))).mapIso e).hom))
  calc
    Module.finrank k G.algebra = G.scheme.hom.finrank x := (finite_group_geometric_rank G x).symm
    _ = (e.hom.left ≫ H.scheme.hom).finrank x := congrArg (fun u => u.finrank x) e.hom.w.symm
    _ = H.scheme.hom.finrank x :=
      congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left H.scheme.hom) x
    _ = Module.finrank k H.algebra := finite_group_geometric_rank H x

theorem finite_group_fiber_rank {X S : Scheme} (f : X ⟶ S) [IsFinite f] [Flat f]
    {k : Type} [Field k] (p : Spec (.of k) ⟶ S)
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    (e : H.scheme ≅ Over.mk (pullback.snd f p)) (x : Spec (.of k)) :
    Module.finrank k H.algebra = f.finrank (p x) := by
  have : IsIso e.hom.left := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of k))).mapIso e).hom))
  calc
    Module.finrank k H.algebra = H.scheme.hom.finrank x := (finite_group_geometric_rank H x).symm
    _ = (e.hom.left ≫ pullback.snd f p).finrank x := congrArg (fun u => u.finrank x) e.hom.w.symm
    _ = (pullback.snd f p).finrank x :=
      congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left (pullback.snd f p)) x
    _ = f.finrank (p x) := Scheme.Hom.finrank_pullback_snd f p x

theorem finite_flat_rank_specializes {X S : Scheme}
    (f : X ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {x y : S} (hxy : x ⤳ y) : f.finrank x = f.finrank y :=
  (hxy.map f.isLocallyConstant_finrank.continuous).eq

theorem finite_flat_rank_on_component {X S : Scheme}
    (f : X ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (x y : S) (hy : y ∈ connectedComponent x) : f.finrank y = f.finrank x :=
  f.isLocallyConstant_finrank.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hy mem_connectedComponent

/-- Once the geometric finite-flat block family and its characteristic-zero
rank have been proved, every specializing FiniteEtale presentation has that rank. -/
theorem finite_group_rank_of_specialization {X S : Scheme}
    (f : X ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {k : Type} [Field k] (p : Spec (.of k) ⟶ S)
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    (e : H.scheme ≅ Over.mk (pullback.snd f p))
    (x : S) (y : Spec (.of k)) (hxy : x ⤳ p y) (r : ℕ) (hr : f.finrank x = r) :
    Module.finrank k H.algebra = r :=
  (finite_group_fiber_rank f p H e y).trans ((finite_flat_rank_specializes f hxy).symm.trans hr)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RankSpecialization
