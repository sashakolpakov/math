import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # Flag Composites -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual marked polarized isogenies along geometric flags and their
composites, with the stated cumulative multipliers and chosen kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

section

def PELModuli.PELFamilyIso.ofEq {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
    {A B : PEL.PELFamilyData R g N S} (h : A = B) : PELModuli.PELFamilyIso A B := h ▸ PELModuli.PELFamilyIso.refl A

theorem PELModuli.PELFamilyIso.ofEq_abelian_hom {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
    {A B : PEL.PELFamilyData R g N S} (h : A = B) :
    (PELModuli.PELFamilyIso.ofEq h).abelian.hom = eqToHom (congrArg (fun C => C.abelian.scheme) h) := by
  subst B
  rfl

end

variable {s : ℕ}

theorem FlagComposites.cumulativeMultiplier_nonneg (ts : List (Local.IntegralType s))
    (j : Fin (ts.length + 1)) : 0 ≤ Local.cumulativeMultiplier ts j := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
  exact t.property.1

theorem FlagComposites.cumulativeMultiplier_succ (ts : List (Local.IntegralType s)) (j : Fin ts.length) :
    Local.cumulativeMultiplier ts j.succ = Local.cumulativeMultiplier ts j.castSucc +
      (ts.get j).val.multiplier := by
  simp only [Local.cumulativeMultiplier, Fin.val_succ, Fin.val_castSucc,
    List.take_succ_eq_append_getElem j.isLt, List.map_append, List.map_singleton,
    List.sum_append, List.sum_singleton, List.get_eq_getElem]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)}
  {x : D.GeometricPoint b} {ts : List (Local.IntegralType s)}

theorem Data.SphericalPELAlbaneseData.flagMultiplier_zero (ts : List (Local.IntegralType s)) : Data.SphericalPELAlbaneseData.flagMultiplier ts 0 = 0 := by
  simp [Data.SphericalPELAlbaneseData.flagMultiplier, Local.cumulativeMultiplier]

theorem Data.SphericalPELAlbaneseData.flagMultiplier_succ (ts : List (Local.IntegralType s)) (j : Fin ts.length) :
    Data.SphericalPELAlbaneseData.flagMultiplier ts j.succ = Data.SphericalPELAlbaneseData.flagMultiplier ts j.castSucc + (ts.get j).multiplierNat := by
  rw [Data.SphericalPELAlbaneseData.flagMultiplier, FlagComposites.cumulativeMultiplier_succ,
    Int.toNat_add (FlagComposites.cumulativeMultiplier_nonneg ts j.castSucc) (ts.get j).property.1]
  rfl

def Data.SphericalPELAlbaneseData.c46FlagSteps (h : D.RealizesIsogenyQuotient) (F : D.PELFlag b x ts) : D.StepSystem F :=
  fun j => D.c46FiberIsogeny h (ts.get j) (F.point j.castSucc) (F.point j.succ)
    (F.branch j) (F.source j) (F.target j)

def Data.SphericalPELAlbaneseData.initialFlagIsogeny (F : D.PELFlag b x ts) :
    PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b (F.point 0)) (q ^ Data.SphericalPELAlbaneseData.flagMultiplier ts 0) :=
  (PELModuli.PELFamilyIso.ofEq (congrArg (D.fiberFamily b) F.start.symm)).toIsogeny.castMultiplier
    (by rw [Data.SphericalPELAlbaneseData.flagMultiplier_zero, pow_zero])

theorem Data.SphericalPELAlbaneseData.initialFlagIsogeny_hom (F : D.PELFlag b x ts) :
    (D.initialFlagIsogeny F).isogeny.hom =
      eqToHom (congrArg (fun y => (D.fiberFamily b y).abelian.scheme) F.start.symm) := by
  rw [Data.SphericalPELAlbaneseData.initialFlagIsogeny, PELIsogenies.PELIsogeny.castMultiplier_hom]
  exact PELModuli.PELFamilyIso.ofEq_abelian_hom _

def Data.SphericalPELAlbaneseData.compositeFromSteps (F : D.PELFlag b x ts) (f : D.StepSystem F) : D.CompositeSystem F :=
  Fin.induction (D.initialFlagIsogeny F) fun j p =>
    (p.comp (f j)).castMultiplier (by rw [Data.SphericalPELAlbaneseData.flagMultiplier_succ, pow_add])

theorem Data.SphericalPELAlbaneseData.compositeFromSteps_zero (F : D.PELFlag b x ts) (f : D.StepSystem F) :
    D.compositeFromSteps F f 0 = D.initialFlagIsogeny F := rfl

theorem Data.SphericalPELAlbaneseData.compositeFromSteps_succ_hom (F : D.PELFlag b x ts) (f : D.StepSystem F)
    (j : Fin ts.length) :
    (D.compositeFromSteps F f j.succ).isogeny.hom =
      (D.compositeFromSteps F f j.castSucc).isogeny.hom ≫ (f j).isogeny.hom := by
  change ((D.compositeFromSteps F f j.castSucc).comp (f j) |>.castMultiplier _).isogeny.hom = _
  rw [PELIsogenies.PELIsogeny.castMultiplier_hom]
  rfl

theorem Data.SphericalPELAlbaneseData.compositeFromSteps_succ_dualHom (F : D.PELFlag b x ts) (f : D.StepSystem F)
    (j : Fin ts.length) :
    (D.compositeFromSteps F f j.succ).dualHom =
      (f j).dualHom ≫ (D.compositeFromSteps F f j.castSucc).dualHom := by
  change ((D.compositeFromSteps F f j.castSucc).comp (f j) |>.castMultiplier _).dualHom = _
  rw [PELIsogenies.PELIsogeny.castMultiplier_dualHom]
  rfl

def Data.SphericalPELAlbaneseData.c46FlagComposites (h : D.RealizesIsogenyQuotient) (F : D.PELFlag b x ts) : D.CompositeSystem F :=
  D.compositeFromSteps F (D.c46FlagSteps h F)

theorem Data.SphericalPELAlbaneseData.c46FlagComposites_isCompositeSystem (h : D.RealizesIsogenyQuotient) (F : D.PELFlag b x ts) :
    D.IsCompositeSystem h F (D.c46FlagComposites h F) (D.c46FlagSteps h F) := by
  refine ⟨D.initialFlagIsogeny_hom F, fun j => ?_⟩
  refine ⟨D.compositeFromSteps_succ_hom F _ j, D.compositeFromSteps_succ_dualHom F _ j, ?_⟩
  intro v
  exact D.c46FiberIsogeny_kernel h (ts.get j) _ _ (F.branch j) (F.source j) (F.target j) v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
