import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseAmpleAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism

/-! # Power Sections And Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerSectionsAndVanishing

noncomputable section

/-! One constructed positive power of an ample line bundle has both
a finite generating section family and vanishing positive cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ample_exists_power_sections_and_vanishing
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ (d : ℕ) (_ : 0 < d) (n : ℕ)
      (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf)),
      (∀ x : X, ∃ i, x ∈ LineBundles.sectionNonvanishing (s i)) ∧
      ∀ q : ℕ, 0 < q → Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.tensorPower d).sheaf q) := by
  obtain ⟨d, hd, n, s, hs, _⟩ := hL.projective_section_family
  obtain ⟨b, hb⟩ := Affine.BaseAmpleAcyclicity.ample_lineBundle_eventually_acyclic_affine f (L.tensorPower d)
    (hL.tensorPower d hd)
  let e : ((L.tensorPower d).tensorPower (b + 1)).sheaf ≅
      (L.tensorPower ((b + 1) * d)).sheaf := (L.tensorPowerComposeIso (b + 1) d).symm
  let t := fun i : Fin (n + 1) => TensorPower.Maps.tensorPowerSection (s i) (b + 1) ≫ e.hom
  refine ⟨(b + 1) * d, Nat.mul_pos (Nat.zero_lt_succ b) hd, n, t, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hs x
    refine ⟨i, ?_⟩
    have he : LineBundles.sectionNonvanishing (t i) = LineBundles.sectionNonvanishing (s i) :=
      (Powers.sectionNonvanishing_comp_iso _ e).trans
        (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := L.tensorPower d) (s i)
          (b + 1) (Nat.zero_lt_succ b))
    exact he.symm ▸ hi
  · intro q hq
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((L.tensorPower d).tensorPower (b + 1)).sheaf (q + 1)) :=
      hb (b + 1) (Nat.le_succ b) q
    exact (ConcreteCategory.bijective_of_isIso ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (q + 1)).map e.inv)).injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerSectionsAndVanishing
