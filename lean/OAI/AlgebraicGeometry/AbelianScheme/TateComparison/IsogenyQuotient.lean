import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence

/-! # Isogeny Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-!
The IsogenyQuotient input is the family-level classification of independent chosen
finite etale kernels by the actual correspondence cover. Its universal
isogeny has the Poincare, polarization, action, and marking equations of
IsogenyQuotient. This input contains no flag equivalence or convolution identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

section

variable {s : ℕ}

def Local.IntegralType.multiplierNat (t : Local.IntegralType s) : ℕ := t.val.multiplier.toNat
def Local.IntegralType.exponentNat (t : Local.IntegralType s) (v : Fin s) (i : Fin 3) : ℕ :=
  (t.val.exponent v i).toNat

@[simp] theorem Local.IntegralType.multiplierNat_cast (t : Local.IntegralType s) :
    (t.multiplierNat : ℤ) = t.val.multiplier := Int.toNat_of_nonneg t.property.1

@[simp] theorem Local.IntegralType.exponentNat_cast (t : Local.IntegralType s) (v : Fin s) (i : Fin 3) :
    (t.exponentNat v i : ℤ) = t.val.exponent v i :=
  Int.toNat_of_nonneg (t.property.2 v i).1

theorem Local.IntegralType.exponentNat_le (t : Local.IntegralType s) (v : Fin s) (i : Fin 3) :
    t.exponentNat v i ≤ t.multiplierNat := by
  exact Int.toNat_le_toNat (t.property.2 v i).2

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

abbrev Data.SphericalPELAlbaneseData.sourceFamily (t : Local.IntegralType s) :=
  D.family.pullback (D.correspondence t).source.left

abbrev Data.SphericalPELAlbaneseData.targetFamily (t : Local.IntegralType s) :=
  D.family.pullback (D.correspondence t).target.left

/-- The universal isogeny is genuine PEL geometry over the cover. -/
abbrev Data.SphericalPELAlbaneseData.UniversalIsogeny (t : Local.IntegralType s) :=
  PELIsogenies.PELIsogeny (D.sourceFamily t) (D.targetFamily t) (q ^ t.multiplierNat)

/-- A chosen block of the actual kernel, as a subgroup functor. -/
def Data.SphericalPELAlbaneseData.universalChosenKernel (t : Local.IntegralType s) (f : D.UniversalIsogeny t) (v : Fin s) :
    Subgroups.PointSubgroup (D.sourceFamily t).abelian :=
  (Subgroups.PointSubgroup.kernel f.isogeny.hom).inf
    (Subgroups.splitBlock (D.sourceFamily t) (D.localCharacter (v, false)) t.multiplierNat)

/-- Pulling back a universal kernel along a lift to the correspondence
uses the canonical group-preserving associativity map of fiber products. -/
def Data.SphericalPELAlbaneseData.chosenKernelAtLift (t : Local.IntegralType s) (f : D.UniversalIsogeny t)
    {T : Over (Spec (.of K))} (x : T ⟶ D.space)
    (c : T ⟶ (D.correspondence t).cover) (w : c ≫ (D.correspondence t).source = x)
    (v : Fin s) : Subgroups.PointSubgroup (D.family.pullback x.left).abelian :=
  ((D.universalChosenKernel t f v).pullback c.left).comapHom
    (BaseChangeCoherence.baseChangeFactorIso D.family.abelian c.left (D.correspondence t).source.left x.left
      (congrArg (fun z => z.left) w)).hom

/-- The independent kernel choices contain no quotient or target data. -/
abbrev Data.SphericalPELAlbaneseData.chosenKernels (t : Local.IntegralType s) {T : Over (Spec (.of K))} (x : T ⟶ D.space) :=
  Subgroups.KernelChoices (D.family.pullback x.left) (fun v => D.localCharacter (v, false))
    t.multiplierNat t.exponentNat

/-- Exactly the one-step IsogenyQuotient realization data. Classification is on all
reduced test schemes, by chosen kernels, and includes repeated geometric
targets through distinct cover points. No correspondence-composition
compatibility is assumed here. -/
def Data.SphericalPELAlbaneseData.RealizesIsogenyQuotient : Prop :=
  ∀ t : Local.IntegralType s, ∃ f : D.UniversalIsogeny t,
    (∀ v, (D.universalChosenKernel t f v).HasFiniteEtaleModel ∧
      (D.universalChosenKernel t f v).HasGeometricType q (t.exponentNat v)) ∧
    (∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (x : T ⟶ D.space) (F : D.chosenKernels t x),
      ∃! c : T ⟶ (D.correspondence t).cover,
        ∃ w : c ≫ (D.correspondence t).source = x,
          ∀ v, D.chosenKernelAtLift t f x c w v = F.val v) ∧
    (∀ (p : (D.targetFamily t).abelian.scheme ⟶ (D.targetFamily t).dual.abelian.scheme)
      [IsMonHom p],
      f.isogeny.hom ≫ p ≫ f.dualHom =
        (D.sourceFamily t).polarizationMap.hom ^ (q ^ t.multiplierNat) →
      p = (D.targetFamily t).polarizationMap.hom)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
