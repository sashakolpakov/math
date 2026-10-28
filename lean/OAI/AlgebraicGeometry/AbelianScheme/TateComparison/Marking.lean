import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

/-! # Marking -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The central marking change is a genuine automorphism of the full
level labels. It changes the universal family's marking; it makes no
assertion that the induced Albanese endomorphism is multiplication by q. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Multiplication by a unit on all ordered full-level labels. -/
def Marking.levelLabelAut (g N : ℕ) (a : (ZMod N)ˣ) :
    Multiplicative (Fin (2 * g) → ZMod N) ≃*
      Multiplicative (Fin (2 * g) → ZMod N) :=
  (LinearEquiv.smulOfUnit (M := Fin (2 * g) → ZMod N) a).toAddEquiv.toMultiplicative

def Marking.locallyConstantMulAut {G : Type*} [Group G] (X : Type*) [TopologicalSpace X]
    (e : G ≃* G) : LocallyConstant X G ≃* LocallyConstant X G where
  toEquiv := LocallyConstant.congrRight e.toEquiv
  map_mul' f g := by
    apply LocallyConstant.ext
    intro x
    exact e.map_mul (f x) (g x)

/-- The label automorphisms are natural in every test scheme. -/
def Marking.levelScalarIso (g N : ℕ) (S : Scheme.{u}) (a : (ZMod N)ˣ) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ≅ AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S :=
  NatIso.ofComponents (fun T =>
    (Marking.locallyConstantMulAut T.unop.left (Marking.levelLabelAut g N a)).toGrpIso) (by
      intro T U f
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro c
      apply LocallyConstant.ext
      intro x
      rfl)

theorem Marking.levelScalarIso_q_apply (g N q : ℕ) (hq : Nat.Coprime q N)
    (S : Scheme.{u}) (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Marking.levelScalarIso g N S (ZMod.unitOfCoprime q hq)).hom.app (.op T) c = c ^ q := by
  apply LocallyConstant.ext
  intro x
  change Multiplicative.ofAdd
    ((ZMod.unitOfCoprime q hq : ZMod N) • (c x).toAdd) = (c x) ^ q
  rw [ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul]
  rfl

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}

/-- An actual change of the ordered full marking by an invertible scalar. -/
abbrev PEL.PELFamilyData.shiftMarking (D : PEL.PELFamilyData R g N S) (a : (ZMod N)ˣ) :
    PEL.PELFamilyData R g N S :=
  { D with marking := Marking.levelScalarIso g N S a ≪≫ D.marking }

/-- For the q-scalar shift, the new marking is obtained by multiplication
by q on the actual torsion points of the universal abelian family. -/
theorem PEL.PELFamilyData.shiftMarking_q_points (D : PEL.PELFamilyData R g N S) (q : ℕ)
    (hq : Nat.Coprime q N) (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    ((D.shiftMarking (ZMod.unitOfCoprime q hq)).marking.hom.app (.op T) c).val =
      (D.marking.hom.app (.op T) c).val ^ q := by
  change (D.marking.hom.app (.op T)
    ((Marking.levelScalarIso g N S (ZMod.unitOfCoprime q hq)).hom.app (.op T) c)).val = _
  rw [Marking.levelScalarIso_q_apply]
  exact congrArg (fun z : D.abelian.torsionPoints N T => z.val)
    (map_pow (D.marking.hom.app (.op T)).hom c q)

@[simp]
theorem PEL.PELFamilyData.shiftMarking_isPEL (D : PEL.PELFamilyData R g N S) (a : (ZMod N)ˣ)
    (δ : Fin g → ℕ) (c : R →+* R) :
    (D.shiftMarking a).IsPEL δ c ↔ D.IsPEL δ c := Iff.rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
