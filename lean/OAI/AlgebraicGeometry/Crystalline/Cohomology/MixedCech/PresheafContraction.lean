import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Coefficients
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HomotopyOppositeUnop

/-! # Presheaf Contraction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.PresheafContraction.MixedCechPresheafContraction

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# Local homotopy equivalences for the Čech presheaf complex

When one member is the whole open, the extra degeneracy acts naturally
on sections over every smaller open. Thus it contracts the presheaf
complex itself, as required for the local step in sheaf descent.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u v

variable (R : Type v) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (P : Presheaf.MixedCechPresheaf.Presheaves R X)

local notation "PS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf.MixedCechPresheaf.Presheaves R X
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf.MixedCechPresheaf.intersectionCoefficients R X P

def intersectionTopIso : Presheaf.MixedCechPresheaf.intersection R X P ⊤ ≅ P :=
  NatIso.ofComponents (fun V => P.mapIso (eqToIso (by
    rw [inf_top_eq]))) (by
      intro V W f
      change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
      rw [← P.map_comp, ← P.map_comp]
      congr 1)

def point : PS :=
  ((FormalCoproduct.evalOp.{u} X.Opens PS).obj Q).obj (op ((FormalCoproduct.incl.{u} X.Opens).obj ⊤))

def pointIso : point R X P ≅ P :=
  (((FormalCoproduct.evalOpCompInlIsoId.{u} X.Opens PS).app Q).app (op ⊤)) ≪≫ intersectionTopIso R X P

variable (i₀ : ι) (hU : U i₀ = ⊤)

def extraDegeneracy :=
  (Cech.Contraction.CechContraction.extraDegeneracy X U i₀ hU).map
    (((FormalCoproduct.evalOp X.Opens PS).obj Q).rightOp)

def oppositeHomotopyEquiv := (extraDegeneracy R X U P i₀ hU).homotopyEquiv

/-- The Čech presheaf complex contracts onto the coefficient presheaf on a split cover. -/
def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ PS).obj P) (Presheaf.MixedCechPresheaf.complex R X U P) :=
  (((HomotopyEquiv.ofIso (HomotopyOppositeUnop.HomotopyOpposite.cofaceIso (Presheaf.MixedCechPresheaf.cosimplicial R X U P)).symm).trans
    (HomotopyOppositeUnop.HomotopyOpposite.unop (oppositeHomotopyEquiv R X U P i₀ hU))).trans
      (HomotopyEquiv.ofIso (HomotopyOppositeUnop.HomotopyOpposite.singleIso (point R X P)))).trans
        (HomotopyEquiv.ofIso ((CochainComplex.single₀ PS).mapIso (pointIso R X P))) |>.symm

/-- The split Čech contraction survives sheafification. -/
def sheafHomotopyEquiv :=
  (Presheaf.MixedCechPresheaf.sheafification R X).mapHomotopyEquiv (MixedCechPresheafContraction.homotopyEquiv R X U P i₀ hU)

/-- Restricting the family to any member gives a contraction of presheaf complexes. -/
def localHomotopyEquiv (i : ι) :=
  MixedCechPresheafContraction.homotopyEquiv R (U i).toScheme (Cech.Contraction.CechContraction.restrictedFamily X U i)
    (Coefficients.MixedCechCoefficients.restricted X U i R P) i (Cech.Contraction.CechContraction.restrictedFamily_self X U i)

/-- The corresponding local contraction of actual sheaf complexes. -/
def localSheafHomotopyEquiv (i : ι) :=
  (Presheaf.MixedCechPresheaf.sheafification R (U i).toScheme).mapHomotopyEquiv (localHomotopyEquiv R X U P i)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.PresheafContraction.MixedCechPresheafContraction
