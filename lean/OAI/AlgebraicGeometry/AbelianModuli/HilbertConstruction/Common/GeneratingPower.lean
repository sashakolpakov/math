import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwisePowerSectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Generating Power -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A finite positive-power section cover can be raised to one common positive power without changing its nonvanishing opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.common_generating_power_of_finite_cover
    {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) {k : ℕ} (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (s : ∀ i, Line.Bundles.structureModule X ⟶ (L.tensorPower (n i)).sheaf)
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    ∃ (d : ℕ) (_ : 0 < d) (t : Fin k → (Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf)),
      ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i) := by
  classical
  let d := ∏ i, n i
  have hd : 0 < d := Finset.prod_pos (fun i _ => hn i)
  have hdiv (i : Fin k) : n i ∣ d := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  let q : Fin k → ℕ := fun i => d / n i
  have hq (i : Fin k) : q i * n i = d := Nat.div_mul_cancel (hdiv i)
  have hqpos (i : Fin k) : 0 < q i := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hzero : d = 0 := (hq i).symm.trans (by rw [hz, zero_mul])
    exact (Nat.ne_of_gt hd) hzero
  let e (i : Fin k) : ((L.tensorPower (n i)).tensorPower (q i)).sheaf ≅ (L.tensorPower d).sheaf :=
    (L.tensorPowerComposeIso (q i) (n i)).symm ≪≫
      eqToIso (congrArg (fun a => (L.tensorPower a).sheaf) (hq i))
  let t (i : Fin k) : Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf :=
    TensorPower.Maps.tensorPowerSection (s i) (q i) ≫ (e i).hom
  have ht (i : Fin k) : Ample.LineBundles.sectionNonvanishing (t i) = Ample.LineBundles.sectionNonvanishing (s i) :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ (e i)).trans
      (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := L.tensorPower (n i)) (s i) (q i) (hqpos i))
  refine ⟨d, hd, t, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨i, (ht i).symm ▸ hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
