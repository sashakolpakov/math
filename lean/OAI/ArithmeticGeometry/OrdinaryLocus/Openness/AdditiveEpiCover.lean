import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveLocalLifts
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Additive Epi Cover -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveEpiCover.Construction

noncomputable section

/-! Finite principal covers on which a section lifts through a sheaf epimorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : CommRingCat.{u})
    (E G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R))) (b : E ⟶ G)

theorem additive_epi_local_principal_lift [hbEpi : Epi b] (s : G.obj.obj (op ⊤)) (p : PrimeSpectrum R) :
    ∃ r : R, p ∈ PrimeSpectrum.basicOpen r ∧
      ∃ t : E.obj.obj (op (PrimeSpectrum.basicOpen r)),
        b.hom.app _ t = G.obj.map (PrimeSpectrum.basicOpen r).leTop.op s := by
  have hb : CategoryTheory.Sheaf.IsLocallySurjective b :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} b).mpr hbEpi
  obtain ⟨U, i, ⟨t, ht⟩, hp⟩ := hb.imageSieve_mem s p (by trivial)
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨r, hpr, E.obj.map (homOfLE hrU).op t, ?_⟩
  have hn := NatTrans.naturality_apply b.hom (homOfLE hrU).op t
  refine hn.trans ?_
  rw [ht]
  have hc : G.obj.map (PrimeSpectrum.basicOpen r).leTop.op =
      G.obj.map i.op ≫ G.obj.map (homOfLE hrU).op :=
    G.obj.map_comp i.op (homOfLE hrU).op
  exact (congrArg (fun q : G.obj.obj (op ⊤) ⟶ G.obj.obj (op (PrimeSpectrum.basicOpen r)) ↦ q s) hc).symm

theorem additive_epi_finite_principal_lifts [Epi b] (s : G.obj.obj (op ⊤)) :
    ∃ (q : Finset (PrimeSpectrum R)) (f : q → R),
      Ideal.span (Set.range f) = ⊤ ∧
        ∃ x : AdditiveCech.Construction.additiveAffineC0 R E f, AdditiveCech.Construction.additiveAffineMap0 R E f b x = AdditiveCech.Construction.additiveAffineUnit R G f s := by
  classical
  choose r hr t ht using additive_epi_local_principal_lift R E G b s
  obtain ⟨q, hq⟩ := isCompact_univ.elim_finite_subcover
    (fun p : PrimeSpectrum R ↦ (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)))
    (fun p ↦ (PrimeSpectrum.basicOpen (r p)).isOpen)
    (fun p _ ↦ Set.mem_iUnion.mpr ⟨p, hr p⟩)
  refine ⟨q, fun p ↦ r p.1, ?_, fun p ↦ t p.1, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_unique
    intro p _
    obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp (hq (Set.mem_univ p))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hpj⟩
  · funext p
    exact ht p.1

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveEpiCover.Construction
