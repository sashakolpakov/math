import OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersion
import OAI.AlgebraicGeometry.SheafCohomology.API
import OAI.AlgebraicGeometry.SheafCohomology.FlasqueVanishing

/-! # Closed Immersion Cohomology -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersionCohomology

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false

namespace ProjectiveVanishing

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Closed-immersion cohomology

Cohomological consequences of closed inclusions used in the Grothendieck vanishing proof.

## Main results

* `PushforwardHIso` — pushforward along a closed inclusion preserves sheaf cohomology, as
 an isomorphism in every degree.
* `subsingleton_sheafH_of_closedImmersion_middle` — vanishing of `Hⁿ` of the middle term in
 the closed-immersion short exact sequence, given vanishing for the kernel and the pullback.

The closed-inclusion stalk, exactness, and adjunction-unit short exact sequence API live
in `ClosedImmersion.lean`. LES-facing `Sheaf.H` wrappers come from `CohomologyAPI.lean`,
and the flasque infrastructure from `FlasqueVanishing.lean`.
-/

universe u

open Abelian Limits

/-! ## Closed-immersion cohomology consequences -/

/-- Pushforward along a closed inclusion preserves sheaf cohomology in every degree, as an
isomorphism. The proof is by induction: in degree zero via sections, in degree one via the
cokernel model of `H¹`, and in higher degrees via dimension-shift isomorphisms on both
sides combined with the induction hypothesis on the next term of an injective resolution. -/
noncomputable def PushforwardHIso
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H G n) ≅
      AddCommGrpCat.of (Sheaf.H ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (ClosedImmersion.ProjectiveVanishing.TopCat.closedIncl hZ)).obj G) n) := by
  let closedIncl := ClosedImmersion.ProjectiveVanishing.TopCat.closedIncl hZ
  induction n generalizing G with
  | zero =>
    exact by
      exact
        (API.ProjectiveVanishing.sheafH0NatIsoSections (X := TopCat.of Z)).app G ≪≫
          ((API.ProjectiveVanishing.sheafH0NatIsoSections (X := X)).app
            ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj G)).symm
  | succ k ih_push =>
    classical
    let ip : InjectivePresentation G := Classical.choice (EnoughInjectives.presentation G)
    let S := ip.shortComplex
    let SX := S.map (Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl)
    have hSE_X : SX.ShortExact :=
      ClosedImmersion.ProjectiveVanishing.closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    have hFlasqueSX₂ : FlasqueVanishing.Projective.IsFlasqueSheaf SX.X₂ := fun j ↦ by
      change Epi (S.X₂.obj.map ((Opens.map closedIncl).op.map j.op))
      exact (FlasqueVanishing.Projective.isFlasque_of_injective S.X₂) ((Opens.map closedIncl).map j)
    have hSE : S.ShortExact := by simpa [S] using ip.shortExact_shortComplex
    have hSrcSub (r : ℕ) : Subsingleton (Sheaf.H S.X₂ (r + 1)) :=
      API.ProjectiveVanishing.sheafH_subsingleton_of_injective S.X₂ r
    have hTgtSub (r : ℕ) : Subsingleton (Sheaf.H SX.X₂ (r + 1)) :=
      FlasqueVanishing.Projective.sheafH_subsingleton_of_flasque X SX.X₂ hFlasqueSX₂ r
    cases k with
    | zero =>
      exact by
        exact
          (show cokernel (SX.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H G 1) from by
            simpa [S, SX, Opens.map_top closedIncl] using
              API.ProjectiveVanishing.sheafH1_cokernel_iso_of_subsingleton_middle hSE (hSrcSub 0)).symm ≪≫
          API.ProjectiveVanishing.sheafH1_cokernel_iso_of_subsingleton_middle hSE_X (hTgtSub 0)
    | succ m =>
      exact by
        exact
          (API.ProjectiveVanishing.sheafH_succ_iso_of_subsingleton_middle hSE (m + 1) (hSrcSub m)
            (hSrcSub (m + 1))).symm ≪≫
        ih_push S.X₃ ≪≫
          API.ProjectiveVanishing.sheafH_succ_iso_of_subsingleton_middle hSE_X (m + 1) (hTgtSub m)
            (hTgtSub (m + 1))

/-- Closed-immersion step: if the kernel term of the closed-immersion
short exact sequence and the pullback to the closed subset have subsingleton
cohomology in degree `n`, then so does the ambient sheaf. -/
theorem subsingleton_sheafH_of_closedImmersion_middle
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h₁ : Subsingleton
      (Sheaf.H ((ClosedImmersion.ProjectiveVanishing.closedImmersionSES (Z := Z) (hZ := hZ) F).X₁) n))
    (h₃ : Subsingleton
      (Sheaf.H
        ((Vanishing.Projective.TopCat.Sheaf.pullback AddCommGrpCat.{u} (ClosedImmersion.ProjectiveVanishing.TopCat.closedIncl hZ)).obj
          F) n)) :
    Subsingleton (Sheaf.H F n) := by
  let closedIncl := ClosedImmersion.ProjectiveVanishing.TopCat.closedIncl hZ
  let FZ := ((Vanishing.Projective.TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F)
  let S := ClosedImmersion.ProjectiveVanishing.closedImmersionSES (Z := Z) (hZ := hZ) F
  have hSE := ClosedImmersion.ProjectiveVanishing.closedImmersionSES_shortExact (Z := Z) (hZ := hZ) F
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := by
    simpa [S] using h₁
  have h₃' : Subsingleton (Sheaf.H FZ n) := by
    simpa [closedIncl, FZ] using h₃
  have hPush : Subsingleton (Sheaf.H S.X₃ n) := by
    let e :
        Sheaf.H FZ n ≃
          Sheaf.H ((Vanishing.Projective.TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj FZ) n :=
      Equiv.ofBijective (ConcreteCategory.hom (PushforwardHIso Z hZ FZ n).hom)
        (ConcreteCategory.bijective_of_isIso (PushforwardHIso Z hZ FZ n).hom)
    simpa [S, ClosedImmersion.ProjectiveVanishing.closedImmersionSES, closedIncl, FZ] using
      (e.subsingleton_congr).mp h₃'
  have : Mono S.f := hSE.mono_f
  have hCok : Subsingleton (Sheaf.H (cokernel S.f) n) := by
    let hSgCok : IsColimit (CokernelCofork.ofπ S.g S.zero) := hSE.gIsCokernel
    let e :=
      (API.ProjectiveVanishing.sheafCohomologyFunctor X n).mapIso
        ((cokernelIsCokernel S.f).coconePointUniqueUpToIso hSgCok)
    have :
        Subsingleton ↑((API.ProjectiveVanishing.sheafCohomologyFunctor X n).obj
          (CokernelCofork.ofπ S.g S.zero).pt) := by
      simpa [API.ProjectiveVanishing.sheafCohomologyFunctor] using hPush
    exact ⟨fun a b ↦ by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      exact Subsingleton.elim _ _⟩
  exact API.ProjectiveVanishing.subsingleton_sheafH_of_shortExact_middle S.f n h₁' hCok
end ProjectiveVanishing

end OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersionCohomology
