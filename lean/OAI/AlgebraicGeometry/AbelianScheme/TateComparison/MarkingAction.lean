import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Marking
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Marking Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Scalar marking changes form an actual invertible action on PEL
families, preserving their moduli conditions and family isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem MarkingAction.levelScalarIso_one (g N : ℕ) (S : Scheme.{u}) :
    Marking.levelScalarIso g N S 1 = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  let c' : LocallyConstant T.unop.left (Multiplicative (Fin (2 * g) → ZMod N)) := c
  apply LocallyConstant.ext
  intro x
  apply Multiplicative.toAdd.injective
  change (1 : ZMod N) • (c' x).toAdd = (c' x).toAdd
  exact one_smul _ _

theorem MarkingAction.levelScalarIso_mul (g N : ℕ) (S : Scheme.{u}) (a b : (ZMod N)ˣ) :
    Marking.levelScalarIso g N S (a * b) = Marking.levelScalarIso g N S a ≪≫ Marking.levelScalarIso g N S b := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  let c' : LocallyConstant T.unop.left (Multiplicative (Fin (2 * g) → ZMod N)) := c
  apply LocallyConstant.ext
  intro x
  apply Multiplicative.toAdd.injective
  change ((a * b : (ZMod N)ˣ) : ZMod N) • (c' x).toAdd =
    (b : ZMod N) • ((a : ZMod N) • (c' x).toAdd)
  rw [Units.val_mul, smul_smul, mul_comm (a : ZMod N) (b : ZMod N)]

section

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
  (D : PEL.PELFamilyData R g N S)

theorem PEL.PELFamilyData.shiftMarking_one : D.shiftMarking 1 = D := by
  let ℓ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ≅ D.abelian.torsionFunctor N := D.marking
  have hm : Marking.levelScalarIso g N S 1 ≪≫ ℓ = ℓ := by
    rw [MarkingAction.levelScalarIso_one]
    exact Iso.refl_trans ℓ
  exact congrArg (fun level : D.abelian.FullLevel N => { D with marking := level }) hm

theorem PEL.PELFamilyData.shiftMarking_mul (a b : (ZMod N)ˣ) :
    (D.shiftMarking a).shiftMarking b = D.shiftMarking (b * a) := by
  let ℓ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ≅ D.abelian.torsionFunctor N := D.marking
  have hm : Marking.levelScalarIso g N S b ≪≫ (Marking.levelScalarIso g N S a ≪≫ ℓ) =
      Marking.levelScalarIso g N S (b * a) ≪≫ ℓ := by
    rw [MarkingAction.levelScalarIso_mul]
    exact (Iso.trans_assoc _ _ _).symm
  exact congrArg (fun level : D.abelian.FullLevel N => { D with marking := level }) hm

def PEL.PELFamilyData.markingShiftEquiv (a : (ZMod N)ˣ) : PEL.PELFamilyData R g N S ≃ PEL.PELFamilyData R g N S where
  toFun D := D.shiftMarking a
  invFun D := D.shiftMarking a⁻¹
  left_inv D := by
    change (D.shiftMarking a).shiftMarking a⁻¹ = D
    rw [PEL.PELFamilyData.shiftMarking_mul, inv_mul_cancel, PEL.PELFamilyData.shiftMarking_one]
  right_inv D := by
    change (D.shiftMarking a⁻¹).shiftMarking a = D
    rw [PEL.PELFamilyData.shiftMarking_mul, mul_inv_cancel, PEL.PELFamilyData.shiftMarking_one]

def PEL.PELFamilyData.shiftMarkingPullbackIso (a : (ZMod N)ˣ) {T : Scheme.{u}} (f : T ⟶ S) :
    PELModuli.PELFamilyIso ((D.shiftMarking a).pullback f) ((D.pullback f).shiftMarking a) where
  abelian := Iso.refl _
  dual := Iso.refl _
  abelianGroup := inferInstanceAs (IsMonHom (𝟙 (D.abelian.pullback f).scheme))
  dualGroup := inferInstanceAs (IsMonHom (𝟙 (D.dual.abelian.pullback f).scheme))
  polarization := by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  poincare := by simp
  equivariant r := by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  marking U c := by
    have he := (D.abelian.baseChangePointsEquiv f U).injective
      ((PELBaseChange.fullLevel_pullback_basis (D.shiftMarking a).marking f U c).trans
        (PELBaseChange.fullLevel_pullback_basis D.marking f U ((Marking.levelScalarIso g N T a).hom.app (.op U) c)).symm)
    exact (Category.comp_id _).trans he

end

section

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
  {D E : PEL.PELFamilyData R g N S}

def PELModuli.PELFamilyIso.shiftMarking (e : PELModuli.PELFamilyIso D E) (a : (ZMod N)ˣ) :
    PELModuli.PELFamilyIso (D.shiftMarking a) (E.shiftMarking a) where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  equivariant := e.equivariant
  marking T c := e.marking T ((Marking.levelScalarIso g N S a).hom.app (.op T) c)

end

theorem MarkingAction.shiftMarking_isPELFamily
    {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s N : ℕ} {S : Scheme.{u}} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (base : NumberField.RingOfIntegers E →+* Γ(S, ⊤))
    (D : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N S) (a : (ZMod N)ˣ) :
    PELModuli.IsPELFamily P base (D.shiftMarking a) ↔ PELModuli.IsPELFamily P base D := Iff.rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
