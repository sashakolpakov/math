import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

/-! # Power Stability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness is invariant under positive tensor powers, with finite affine covers in one degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X Y : Scheme.{u}} {L : Line.Bundles.LineBundle X}

/-- The two possible orders of iterated powers are canonically isomorphic. -/
def Line.Bundles.LineBundle.tensorPowerSwapIso (L : Line.Bundles.LineBundle X) (m n : ℕ) :
    ((L.tensorPower n).tensorPower m).sheaf ≅ ((L.tensorPower m).tensorPower n).sheaf :=
  (L.tensorPowerComposeIso m n).symm ≪≫
    eqToIso (congrArg (fun d => (L.tensorPower d).sheaf) (Nat.mul_comm m n)) ≪≫
      L.tensorPowerComposeIso n m

/-- Every positive tensor power of an ample line bundle is ample. -/
theorem Line.Bundles.LineBundle.IsAmple.tensorPower (hL : L.IsAmple) (m : ℕ) (hm : 0 < m) :
    (L.tensorPower m).IsAmple := by
  obtain ⟨hX, h⟩ := (L.isAmple_iff_tensorPower).mp hL
  apply ((L.tensorPower m).isAmple_iff_tensorPower).mpr
  refine ⟨hX, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, hs⟩ := h x
  let t := TensorPower.Maps.tensorPowerSection s m ≫ (L.tensorPowerSwapIso m n).hom
  have he : Ample.LineBundles.sectionNonvanishing t = Ample.LineBundles.sectionNonvanishing s :=
    (Ample.Powers.sectionNonvanishing_comp_iso _ (L.tensorPowerSwapIso m n)).trans
      (Section.PowerLocus.sectionNonvanishing_tensorPowerSection (L := L.tensorPower n) s m hm)
  exact ⟨n, hn, t, he.symm ▸ hx, he.symm ▸ hs⟩

/-- If a positive power is ample, the original line bundle is ample. -/
theorem Line.Bundles.LineBundle.IsAmple.of_tensorPower (m : ℕ) (hm : 0 < m) (hL : (L.tensorPower m).IsAmple) :
    L.IsAmple := by
  obtain ⟨hX, h⟩ := ((L.tensorPower m).isAmple_iff_tensorPower).mp hL
  apply L.isAmple_iff_tensorPower.mpr
  refine ⟨hX, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, hs⟩ := h x
  let t := s ≫ (L.tensorPowerComposeIso n m).inv
  have he : Ample.LineBundles.sectionNonvanishing t = Ample.LineBundles.sectionNonvanishing s :=
    Ample.Powers.sectionNonvanishing_comp_iso s (L.tensorPowerComposeIso n m).symm
  exact ⟨n * m, Nat.mul_pos hn hm, t, he.symm ▸ hx, he.symm ▸ hs⟩

theorem Line.Bundles.LineBundle.isAmple_tensorPower_iff (L : Line.Bundles.LineBundle X) (m : ℕ) (hm : 0 < m) :
    (L.tensorPower m).IsAmple ↔ L.IsAmple :=
  ⟨Line.Bundles.LineBundle.IsAmple.of_tensorPower m hm, fun h => h.tensorPower m hm⟩

/-- Relative ampleness is also invariant under positive powers. -/
theorem Line.Bundles.LineBundle.isRelativelyAmple_tensorPower_iff (L : Line.Bundles.LineBundle X) (f : X ⟶ Y)
    (m : ℕ) (hm : 0 < m) :
    (L.tensorPower m).IsRelativelyAmple f ↔ L.IsRelativelyAmple f := by
  constructor
  · intro h U hU
    exact Line.Bundles.LineBundle.IsAmple.of_tensorPower m hm ((h U hU).of_iso (L.tensorPowerPullbackIso m (f ⁻¹ᵁ U).ι))
  · intro h U hU
    exact ((h U hU).tensorPower m hm).of_iso (L.tensorPowerPullbackIso m (f ⁻¹ᵁ U).ι).symm

/-- An ample line bundle has a finite affine nonvanishing cover by sections of one positive power. -/
theorem Line.Bundles.LineBundle.IsAmple.finite_common_power_cover (hL : L.IsAmple) :
    ∃ (d : ℕ) (_ : 0 < d) (k : ℕ)
      (s : Fin k → (Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf)),
      (∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) ∧
        ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  obtain ⟨k, n, hn, s, hs, hcover⟩ := hL.finite_tensorPower_cover
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
  refine ⟨d, hd, k, t, fun i => (ht i).symm ▸ hs i, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨i, (ht i).symm ▸ hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
