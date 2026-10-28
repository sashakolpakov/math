import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalLifts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Local Primitives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalPrimitives.CrystallineLocalPrimitives

noncomputable section

/-!
# Finite principal local primitives in exact native sheaf complexes

A cycle section of an exact short complex of native Witt-module sheaves
has a primitive on a finite unit-ideal principal cover. The cycles object
is evaluated using preservation of kernels; the surjection onto cycles is
then lifted on the actual native site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

def evaluation (Q : Site.Object p k X) : Sheaf J V ⥤ V :=
  sheafToPresheaf J V ⋙ (CategoryTheory.evaluation _ _).obj (op Q)

instance evaluation_preservesLimits (Q : Site.Object p k X) :
    PreservesLimits (CrystallineLocalPrimitives.evaluation p k X Q) := by
  dsimp [CrystallineLocalPrimitives.evaluation]
  infer_instance

instance evaluation_additive (Q : Site.Object p k X) :
    (CrystallineLocalPrimitives.evaluation p k X Q).Additive := by
  dsimp [CrystallineLocalPrimitives.evaluation]
  infer_instance

theorem cycle_lift (S : ShortComplex (Sheaf J V)) (Q : Site.Object p k X)
    (x : S.X₂.obj.obj (op Q)) (hx : S.g.hom.app (op Q) x = 0) :
    ∃ y : S.cycles.obj.obj (op Q), S.iCycles.hom.app (op Q) y = x := by
  let K := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hK : K.Exact := K.exact_of_f_is_kernel S.cyclesIsKernel
  have he := hK.map_of_mono_of_preservesKernel (CrystallineLocalPrimitives.evaluation p k X Q)
    (inferInstance : Mono K.f) inferInstance
  exact (ShortComplex.moduleCat_exact_iff (K.map (CrystallineLocalPrimitives.evaluation p k X Q))).mp he x hx

theorem exists_principal_primitives (S : ShortComplex (Sheaf J V)) (hS : S.Exact)
    (Q : Site.Object p k X) (x : S.X₂.obj.obj (op Q))
    (hx : S.g.hom.app (op Q) x = 0) :
    ∃ t : Finset Q.thickening.ring, Ideal.span (t : Set Q.thickening.ring) = ⊤ ∧
      ∀ s : t, ∃ y : S.X₁.obj.obj (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s.val)),
        S.f.hom.app _ y = S.X₂.obj.map
          (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val).op x := by
  obtain ⟨z, hz⟩ := cycle_lift p k X S Q x hx
  have : Epi S.toCycles := hS.epi_toCycles
  obtain ⟨t, ht, hlift⟩ := LocalLifts.CrystallineLocalLifts.exists_principal_lifts p k X S.toCycles Q z
  refine ⟨t, ht, fun s => ?_⟩
  obtain ⟨y, hy⟩ := hlift s
  refine ⟨y, ?_⟩
  have hfac := congrArg (fun f => f.hom.app
    (op (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s.val)) y) S.toCycles_i
  have hnat := congrArg (fun f => f z)
    (S.iCycles.hom.naturality (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s.val).op)
  change S.iCycles.hom.app _ (S.toCycles.hom.app _ y) = S.f.hom.app _ y at hfac
  change S.iCycles.hom.app _ (S.cycles.obj.map _ z) =
    S.X₂.obj.map _ (S.iCycles.hom.app _ z) at hnat
  rw [← hfac, hy, hnat, hz]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalPrimitives.CrystallineLocalPrimitives
