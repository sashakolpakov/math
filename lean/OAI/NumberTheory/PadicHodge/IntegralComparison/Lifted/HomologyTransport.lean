import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyCoordinates

/-! # Homology Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyTransport

noncomputable section

/-! Canonical cohomology coordinates remain natural after a comparison with an independently defined module. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type u) [CommRing R]
  {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (i : ℕ)
  {A B : ModuleCat.{max v w} R}
  (e : (HomologyCoordinates.complex.{u, v, w} R K).homology i ≅ A)
  (d : (HomologyCoordinates.complex.{u, v, w} R L).homology i ≅ B) (g : A ⟶ B)
  (h : HomologicalComplex.homologyMap (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex (.up ℕ)).map f) i ≫
    d.hom = e.hom ≫ g)

include h in
theorem naturality (x : K.homology i) :
    ((HomologyCoordinates.equivalence.{u, v, w} R L i).trans d.toLinearEquiv)
      (HomologicalComplex.homologyMap f i x) =
        g (((HomologyCoordinates.equivalence.{u, v, w} R K i).trans e.toLinearEquiv) x) :=
  (congrArg d.hom (HomologyCoordinates.naturality.{u, v, w} R f i x).symm).trans
    (congrArg (fun a => a (HomologyCoordinates.equivalence.{u, v, w} R K i x)) h)

include h in
theorem combined_naturality (x : K.homology i) :
    (ULift.moduleEquiv.symm.trans
      ((((L.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{w, v} R)).symm ≪≫ d).toLinearEquiv))
        (HomologicalComplex.homologyMap f i x) =
      g ((ULift.moduleEquiv.symm.trans
        ((((K.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{w, v} R)).symm ≪≫ e).toLinearEquiv)) x) :=
  naturality R f i e d g h x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyTransport
