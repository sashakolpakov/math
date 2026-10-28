import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulBasisResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Forget
import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution

noncomputable section

/-! The normal-to-point Koszul inclusion is an actual lift of the
quotient map. Hence its dual computes the canonical Ext map, with
arbitrary target coefficients and independent of resolution choices. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
variable (R : Type u) [CommRing R] {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

abbrev normalIdeal := Koszul.OrientedTopCohomology.ideal R s
abbrev pointIdeal := Exterior.KoszulBasisResolution.ideal R
  (TopResidue.basis R) (Differential.equation R s t)

theorem basis_values : (fun i => Differential.equation R s t (TopResidue.basis R i)) =
    Fin.append s t := by
  rw [TopResidue.basis_append]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Differential.equation, Koszul.GeneratorMatrix.equation_apply, Pi.basisFun_apply, Pi.single_apply]
  · simp [Differential.equation, Koszul.GeneratorMatrix.equation_apply, Pi.basisFun_apply, Pi.single_apply]

theorem ideal_le : normalIdeal R s ≤ pointIdeal R s t := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  apply Ideal.subset_span
  refine ⟨Fin.castAdd m i, ?_⟩
  exact (congrFun (basis_values R s t) (Fin.castAdd m i)).trans (by simp)

def quotient : ModuleCat.of R (R ⧸ normalIdeal R s) ⟶ ModuleCat.of R (R ⧸ pointIdeal R s t) :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    exact ideal_le R s t hx))

abbrev normalResolution (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s)) :=
  Exterior.KoszulResolution.resolution R s hs

def pointResolution
    (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t))) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ pointIdeal R s t)) :=
  Exterior.KoszulBasisResolution.resolution R (TopResidue.basis R)
    (Differential.equation R s t) (by rw [basis_values]; exact hst)

def inclusion : Koszul.OrientedTopCohomology.koszul R s ⟶
    Exterior.KoszulComplex.complex R (Fractions.ambient R (c := c) (m := m)) (Differential.equation R s t) :=
  Exterior.KoszulComplex.map R _ _ _ _ (LinearMap.inl R _ _) (Differential.equation_inl R s t)

theorem augmentation
    (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
    (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t))) :
    inclusion R s t ≫ (pointResolution R s t hst).π =
      (normalResolution R s hs).π ≫ (ChainComplex.single₀ (ModuleCat R)).map (quotient R s t) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        Exterior.KoszulResolution.resolution_π_f_zero,
        ChainComplex.single₀_map_f_zero]
      change (inclusion R s t).f 0 ≫
        (Exterior.KoszulBasisResolution.resolution R (TopResidue.basis R)
          (Differential.equation R s t) _).π.f 0 = _
      rw [Exterior.KoszulBasisResolution.resolution_π_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (pointIdeal R s t).mkQ (exteriorPower.zeroEquiv R _
        (exteriorPower.map 0 (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m))) x)) =
          (pointIdeal R s t).mkQ (exteriorPower.zeroEquiv R _ x)
      exact congrArg (pointIdeal R s t).mkQ (LinearMap.congr_fun
        (exteriorPower.zeroEquiv_naturality (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m)))) x)
  | succ n =>
      exact (isZero_single_obj_X (.down ℕ) 0
        (ModuleCat.of R (R ⧸ pointIdeal R s t)) (n + 1) (by omega)).eq_of_tgt _ _

variable {D : Type v} [Category.{w} D] [Abelian D]
  (F : (ModuleCat.{u} R)ᵒᵖ ⥤ D) [F.Additive]
  (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))

theorem canonical_map (n : ℕ) :
    Resolution.CohomologyMaps.map F (normalResolution R s hs) (pointResolution R s t hst)
      (quotient R s t) n =
        IntegralComparison.ProjectiveResolution.HomNaturality.map F (inclusion R s t) n :=
  Resolution.CohomologyMaps.map_eq F _ _ _ _ (augmentation R s t hs hst) n

abbrev arbitrary_resolution
    (P : ProjectiveResolution (ModuleCat.of R (R ⧸ normalIdeal R s)))
    (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ pointIdeal R s t)))
    (a : P.complex ⟶ Q.complex)
    (ha : a ≫ Q.π = P.π ≫ (ChainComplex.single₀ (ModuleCat R)).map (quotient R s t)) (n : ℕ) :=
  IntegralComparison.ProjectiveResolution.HomNaturality.naturality F (quotient R s t) P
    (normalResolution R s hs) Q (pointResolution R s t hst) a
    (inclusion R s t) ha (augmentation R s t hs hst) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
