import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Pullbacks
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Isomorphisms

/-! # Open Refinement -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.OpenRefinement.CrystallinePrincipalOpenRefinement

noncomputable section

/-!
# Refining native open immersions by actual principal opens

If an ambient principal open is contained in the image of a native open
immersion, its principal base change is a native crystalline isomorphism.
Its inverse gives a factorization of the actual principal-open projection
through that native open immersion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {P Q : Site.Object p k X}
  (f : P ⟶ Q) (s : Q.thickening.ring)

local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X
local notation "m" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Pullbacks.CrystallinePrincipalPullbacks.map p k X f s
local notation "πP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s)
local notation "πQ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s

theorem ambient_condition : (A).map m ≫ (A).map πQ = (A).map πP ≫ (A).map f :=
  ((A).map_comp m πQ).symm.trans
    ((congrArg (A).map (Pullbacks.CrystallinePrincipalPullbacks.condition p k X f s)).trans ((A).map_comp πP f))

instance ambient_openImmersion [IsOpenImmersion ((A).map f)] : IsOpenImmersion ((A).map m) := by
  have : IsOpenImmersion ((A).map πP ≫ (A).map f) := inferInstance
  have : IsOpenImmersion ((A).map m ≫ (A).map πQ) :=
    (ambient_condition p k X f s).symm ▸ this
  exact IsOpenImmersion.of_comp _ ((A).map πQ)

theorem ambient_surjective
    (hs : (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Q.thickening.ring)) ⊆
      Set.range (PrimeSpectrum.comap f.ambientMap.toRingHom)) :
    Function.Surjective (PrimeSpectrum.comap (m).ambientMap.toRingHom) := by
  intro y
  let x := PrimeSpectrum.comap (algebraMap Q.thickening.ring (Localization.Away s)) y
  have hx : x ∈ (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Q.thickening.ring)) :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s) ▸ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hs hx
  have hz' : z ∈ (PrimeSpectrum.basicOpen (f.ambientMap s) : Set (PrimeSpectrum P.thickening.ring)) := by
    change s ∉ (PrimeSpectrum.comap f.ambientMap.toRingHom z).asIdeal
    rw [hz]
    exact hx
  have hw : z ∈ Set.range (PrimeSpectrum.comap
      (algebraMap P.thickening.ring (Localization.Away (f.ambientMap s)))) :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away (f.ambientMap s)) (f.ambientMap s)).symm ▸ hz'
  obtain ⟨w, hw⟩ := hw
  refine ⟨w, (Scheme.Hom.isOpenEmbedding ((A).map πQ)).injective ?_⟩
  have hc := congrArg (fun g => g w) (ambient_condition p k X f s)
  change PrimeSpectrum.comap (algebraMap Q.thickening.ring (Localization.Away s))
      (PrimeSpectrum.comap (m).ambientMap.toRingHom w) =
    PrimeSpectrum.comap f.ambientMap.toRingHom
      (PrimeSpectrum.comap (algebraMap P.thickening.ring (Localization.Away (f.ambientMap s))) w) at hc
  exact (hc.trans (congrArg (PrimeSpectrum.comap f.ambientMap.toRingHom) hw)).trans hz

def iso [IsOpenImmersion ((A).map f)]
    (hs : (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Q.thickening.ring)) ⊆
      Set.range (PrimeSpectrum.comap f.ambientMap.toRingHom)) :
    Opens.CrystallinePrincipalOpens.object p k X P (f.ambientMap s) ≅ Opens.CrystallinePrincipalOpens.object p k X Q s :=
  CrystallineOpen.Isomorphisms.CrystallineOpenIsomorphisms.iso p k X m (ambient_surjective p k X f s hs)

def lift [IsOpenImmersion ((A).map f)]
    (hs : (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Q.thickening.ring)) ⊆
      Set.range (PrimeSpectrum.comap f.ambientMap.toRingHom)) :
    Opens.CrystallinePrincipalOpens.object p k X Q s ⟶ P :=
  (iso p k X f s hs).inv ≫ πP

theorem lift_factor [IsOpenImmersion ((A).map f)]
    (hs : (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Q.thickening.ring)) ⊆
      Set.range (PrimeSpectrum.comap f.ambientMap.toRingHom)) :
    lift p k X f s hs ≫ f = πQ := by
  change ((iso p k X f s hs).inv ≫ πP) ≫ f = πQ
  rw [Category.assoc, ← Pullbacks.CrystallinePrincipalPullbacks.condition]
  exact Iso.inv_hom_id_assoc (iso p k X f s hs) πQ

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.OpenRefinement.CrystallinePrincipalOpenRefinement
