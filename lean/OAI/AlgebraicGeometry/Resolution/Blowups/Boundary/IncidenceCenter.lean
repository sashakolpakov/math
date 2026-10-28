import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterSubunions
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformIncidenceTransform

/-! # Incidence Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Canonical finite groups of smooth center components with the same containing boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)

def Boundary.IncidenceCenter.Construction.boundaryIncidenceComponentSet (F : Finset β) : Finset (irreducibleComponents I.subscheme) := by
  classical
  exact Finset.univ.filter (fun C => Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels (Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C) D = F)

def Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter (F : Finset β) : X.IdealSheafData :=
  Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I (Boundary.IncidenceCenter.Construction.boundaryIncidenceComponentSet f I D F)

theorem Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_pairwise (F G : Finset β) (hFG : F ≠ G) :
    Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F ⊔ Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D G = ⊤ := by
  classical
  apply Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_disjoint
  apply Finset.disjoint_left.mpr
  intro C hF hG
  exact hFG ((Finset.mem_filter.mp hF).2.symm.trans (Finset.mem_filter.mp hG).2)

theorem Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product : ∏ F : Finset β, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F = I := by
  classical
  unfold Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal Boundary.IncidenceCenter.Construction.boundaryIncidenceComponentSet
  rw [Finset.prod_fiberwise, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_prod]

theorem Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_ne_bot [IsIntegral X] [IsLocallyNoetherian X]
    (hI : I ≠ ⊥) (F : Finset β) : Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F ≠ ⊥ :=
  Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_ne_bot f I hI _

theorem Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_smooth (F : Finset β) :
    Smooth ((Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).subschemeι ≫ f) :=
  Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_smooth f I _

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.subunion_incidence
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (F : Finset β) (i : A.indices)
    (hproper : (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).ideal (A.opens i) ≠ ⊤) : A.divided i = F := by
  classical
  have hex : ∃ C ∈ Boundary.IncidenceCenter.Construction.boundaryIncidenceComponentSet f I D F,
      (Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C).ideal (A.opens i) ≠ ⊤ := by
    by_contra! h
    apply hproper
    change (∏ C ∈ Boundary.IncidenceCenter.Construction.boundaryIncidenceComponentSet f I D F, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C).ideal (A.opens i) = ⊤
    rw [Global.MixedBoundary.Construction.idealSheaf_finset_prod_ideal]
    rw [Finset.prod_congr rfl h, ← Ideal.one_eq_top, Finset.prod_const_one]
  obtain ⟨C, hC, hp⟩ := hex
  let : IsIntegral (Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C).subscheme := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_integral f I C
  have he := (A.integralComponent f I C).divided_eq_integralCenterBoundaryLabels i hp
  change A.divided i = Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels (Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C) D at he
  exact he.trans (Finset.mem_filter.mp hC).2

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (F : Finset β) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F) D :=
  (A.subunion f I (Boundary.IncidenceCenter.Construction.boundaryIncidenceComponentSet f I D F)).withUniformIncidence F
    (fun i hp => A.subunion_incidence f I D F i hp)

end

section

/-! On each actual boundary chart, an incidence group is either the whole local center or empty. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter_ideal_eq_top (F : Finset β) (i : A.indices)
    (hF : A.divided i ≠ F) : (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).ideal (A.opens i) = ⊤ := by
  by_contra h
  exact hF (A.subunion_incidence f I D F i h)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter_ideal_eq (i : A.indices) :
    (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (A.divided i)).ideal (A.opens i) = I.ideal (A.opens i) := by
  classical
  have he := congrArg (fun K : X.IdealSheafData => K.ideal (A.opens i)) (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product f I D)
  rw [Global.MixedBoundary.Construction.idealSheaf_finset_prod_ideal] at he
  rw [Finset.prod_eq_single (A.divided i)] at he
  · exact he
  · intro F _ hF
    rw [A.incidenceCenter_ideal_eq_top f I D F i hF.symm, Ideal.one_eq_top]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter_ideal_formula [DecidableEq β] (F : Finset β) (i : A.indices) :
    (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).ideal (A.opens i) =
      if A.divided i = F then I.ideal (A.opens i) else ⊤ := by
  classical
  by_cases he : A.divided i = F
  · rw [ite_eq_left he, ← he]
    exact A.incidenceCenter_ideal_eq f I D i
  · rw [ite_eq_right he]
    exact A.incidenceCenter_ideal_eq_top f I D F i he

end

/-! Unions of incidence groups have explicit native ideals and remain smooth boundary-compatible subcenters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] [DecidableEq β] (D : β → X.IdealSheafData)

def Boundary.IncidenceCenter.Construction.selectedIncidenceCenter (s : Finset (Finset β)) : X.IdealSheafData :=
  ∏ F ∈ s, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F

omit [DecidableEq β] in
theorem Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_disjoint (s t : Finset (Finset β)) (hst : Disjoint s t) :
    Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D s ⊔ Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D t = ⊤ := by
  classical
  apply Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top
  intro G hG
  rw [sup_comm]
  apply Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top
  intro F hF
  exact Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_pairwise f I D G F (fun he => Finset.disjoint_left.mp hst hF (he ▸ hG))

theorem Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_factorization (s : Finset (Finset β)) :
    I = Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D s * Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D sᶜ := by
  classical
  rw [Boundary.IncidenceCenter.Construction.selectedIncidenceCenter, Boundary.IncidenceCenter.Construction.selectedIncidenceCenter, Finset.prod_mul_prod_compl,
    Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product]

theorem Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_smooth (s : Finset (Finset β)) :
    Smooth ((Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D s).subschemeι ≫ f) := by
  classical
  let K := Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D s
  let L := Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D sᶜ
  have he : I = L * K := (Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_factorization f I D s).trans (mul_comm K L)
  let : Smooth ((L * K).subschemeι ≫ f) := he ▸ inferInstanceAs (Smooth (I.subschemeι ≫ f))
  exact Blowups.Smooth.ComaximalFactor.Construction.smooth_comaximal_right_factor f L K (Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_disjoint f I D sᶜ s disjoint_compl_left)

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.selectedIncidence
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (s : Finset (Finset β)) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D s) D :=
  A.comaximalFactor _ _ (Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_factorization f I D s)
    (Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_disjoint f I D s sᶜ disjoint_compl_right)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.selectedIncidence_ideal
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (s : Finset (Finset β)) (i : A.indices) :
    (Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D s).ideal (A.opens i) =
      if A.divided i ∈ s then I.ideal (A.opens i) else ⊤ := by
  classical
  rw [Boundary.IncidenceCenter.Construction.selectedIncidenceCenter, Global.MixedBoundary.Construction.idealSheaf_finset_prod_ideal]
  by_cases hi : A.divided i ∈ s
  · rw [ite_eq_left hi, Finset.prod_eq_single (A.divided i)]
    · exact A.incidenceCenter_ideal_eq f I D i
    · intro F _ hF
      rw [A.incidenceCenter_ideal_eq_top f I D F i hF.symm, Ideal.one_eq_top]
    · intro hn
      exact (hn hi).elim
  · rw [ite_eq_right hi, ← Ideal.one_eq_top]
    apply Finset.prod_eq_one
    intro F hF
    rw [A.incidenceCenter_ideal_eq_top f I D F i (fun he => hi (he.symm ▸ hF)), Ideal.one_eq_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
