import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsYZQuotients
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction

/-! # Prescription -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription.Construction

noncomputable section

section

/-! The independent full-kernel prescription, using the actual canonical
polarization pairing on every scheme-valued point. Representability and
polarized quotient existence are conclusions of FrobeniusKernel, not fields here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}

def originalTorsionSheafPoint (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (m : ℕ)
    (T : Over (Spec (.of k))) (x : (A.torsionFunctor m).obj (.op T)) :
    (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A) m).obj.obj (.op T) :=
  (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) m).hom.hom.app (.op T)
    (ULift.up ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A m).inv.app (.op T) x))

/-- Triviality of the actual polarization-induced Weil value; no abstract
perfect pairing or chosen Cartier-duality witness is substituted for it. -/
def canonicalTorsionOrthogonal
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor m).obj (.op T)) : Prop :=
  CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) m) T
    ((CartierDualityCanonical.Construction.e56SourceTorsionPairing A m hm).rightAdjoint.hom.app (.op T)
      (originalTorsionSheafPoint A.abelian m T y))
    (originalTorsionSheafPoint A.abelian m T x) = 1

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def prescribedBlockComponent (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (A.abelian.torsionFunctor (q ^ n)).obj (.op T) :=
  (PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
    ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A.abelian ρ n τ).app (.op T) x)

def prescribedChosenPoint (n : ℕ) (τ : Gal(E/ℚ))
    (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) (h : T ⟶ H.group.X) :
    (A.abelian.torsionFunctor (q ^ n)).obj (.op T) :=
  (PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) (h ≫ H.inclusion.hom.hom))

/-- Each chosen component lies in its prescribed finite subgroup; each
opposite component annihilates that subgroup after every further base
change of the test scheme. The ambient level remains exactly q^n. -/
def prescribedFullKernel (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme) : Prop :=
  ∃ x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T), x.val = a ∧
    (∀ v : Fin s,
      (∃ h : T ⟶ (H v).group.X,
        prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) T h =
          prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) T x) ∧
      ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (h : U ⟶ (H v).group.X),
        canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
          (prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)
          (prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U
            ((A.abelian.torsionFunctor (q ^ n)).map t.op x)))

end

/-! The independent kernel prescription uses every point of the actual
torsion sheaf, through a natural multiplicative equivalence with the
original HilbertConstruction torsion functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (m : ℕ)

def originalTorsionSheafPointMulEquiv (T : Over (Spec (.of k))) :
    (A.torsionFunctor m).obj (.op T) ≃*
      (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A) m).obj.obj (.op T) := by
  let i := ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) CommGrpCat.{1}).mapIso
    (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) m)).app (.op T)
  exact ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A m).app (.op T)).groupIsoToMulEquiv.symm.trans
    (MulEquiv.ulift.symm.trans (((forget₂ CommGrpCat GrpCat).mapIso i).groupIsoToMulEquiv))

theorem originalTorsionSheafPointMulEquiv_apply (T : Over (Spec (.of k)))
    (x : (A.torsionFunctor m).obj (.op T)) :
    originalTorsionSheafPointMulEquiv A m T x = originalTorsionSheafPoint A m T x := rfl

theorem originalTorsionSheafPoint_bijective (T : Over (Spec (.of k))) :
    Function.Bijective (originalTorsionSheafPoint A m T) :=
  (originalTorsionSheafPointMulEquiv A m T).bijective

theorem originalTorsionSheafPoint_mul (T : Over (Spec (.of k)))
    (x y : (A.torsionFunctor m).obj (.op T)) :
    originalTorsionSheafPoint A m T (x * y) =
      originalTorsionSheafPoint A m T x * originalTorsionSheafPoint A m T y :=
  (originalTorsionSheafPointMulEquiv A m T).map_mul x y

theorem originalTorsionSheafPoint_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : (A.torsionFunctor m).obj (.op T)) :
    (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A) m).obj.map t.op
        (originalTorsionSheafPoint A m T x) =
      originalTorsionSheafPoint A m U ((A.torsionFunctor m).map t.op x) := by
  let i := (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A m).inv
  let f := (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) m).hom.hom
  have hf := f.naturality_apply t.op (ULift.up (i.app (.op T) x))
  have hi := i.naturality_apply t.op x
  exact hf.symm.trans (congrArg
    (fun z : U ⟶ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) m).X => f.app (.op U) (ULift.up z)) hi.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription.Construction
