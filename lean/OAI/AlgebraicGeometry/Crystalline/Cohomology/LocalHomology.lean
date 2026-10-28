import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalPrimitives

/-! # Local Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalHomology.CrystallineLocalHomology

noncomputable section

/-!
# Local vanishing of section homology on the native site

The homology of evaluated sheaf complexes need not vanish globally.
For an exact short complex, every such class nevertheless vanishes on
an actual finite unit-ideal principal cover. The maps on these classes
are the canonical homology maps induced by native restrictions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

def evaluationMap {P Q : Site.Object p k X} (f : P ⟶ Q) :
    LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q ⟶
      LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X P :=
  Functor.whiskerLeft (sheafToPresheaf J V) ((CategoryTheory.evaluation _ _).map f.op)

def sectionComplex (S : ShortComplex (Sheaf J V)) (Q : Site.Object p k X) :
    ShortComplex V := S.map (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q)

def restriction (S : ShortComplex (Sheaf J V)) {P Q : Site.Object p k X} (f : P ⟶ Q) :
    sectionComplex p k X S Q ⟶ sectionComplex p k X S P :=
  S.mapNatTrans (evaluationMap p k X f)

theorem exists_principal_vanishing (S : ShortComplex (Sheaf J V)) (hS : S.Exact)
    (Q : Site.Object p k X) (x : (sectionComplex p k X S Q).homology) :
    ∃ t : Finset Q.thickening.ring, Ideal.span (t : Set Q.thickening.ring) = ⊤ ∧
      ∀ s : t, ShortComplex.homologyMap (restriction p k X S
        (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val)) x = 0 := by
  let A := sectionComplex p k X S Q
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective A.homologyπ).mp inferInstance x
  have hcycle : S.g.hom.app (op Q) (A.iCycles z) = 0 := by
    exact congrArg (fun f => f z) A.iCycles_g
  obtain ⟨t, ht, hprim⟩ := LocalPrimitives.CrystallineLocalPrimitives.exists_principal_primitives p k X S hS Q
    (A.iCycles z) hcycle
  refine ⟨t, ht, fun s => ?_⟩
  obtain ⟨y, hy⟩ := hprim s
  let f := CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val
  let T := sectionComplex p k X S (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s.val)
  let φ := restriction p k X S f
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [map_zero, ← hz]
  have hmap := congrArg (fun g => g z) (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι (ShortComplex.homologyMap φ (A.homologyπ z)) =
    T.pOpcycles (φ.τ₂ (A.iCycles z)) at hmap
  rw [hmap]
  apply (T.moduleCat_pOpcycles_eq_zero_iff _).mpr
  exact ⟨y, hy⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalHomology.CrystallineLocalHomology
