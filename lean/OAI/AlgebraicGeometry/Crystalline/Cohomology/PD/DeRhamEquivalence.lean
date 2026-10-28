import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # De Rham Equivalence -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence

noncomputable section

/-!
# Transport of the PD de Rham complex along PD algebra isomorphisms

The form maps constructed earlier give inverse linear maps in every
degree and commute with the differential. Thus a genuine PD algebra
isomorphism induces an isomorphism of the actual de Rham complexes.
-/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R]
  {A B C : CommAlgCat.{u} R}
  {I : Ideal A} {J : Ideal B} {L : Ideal C}
  {δ : DividedPowers I} {ε : DividedPowers J} {ζ : DividedPowers L}

def complexMap (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δ ε f.hom.toRingHom) :
    DeRham.PDDeRham.complex R A I δ ⟶ DeRham.PDDeRham.complex R B J ε where
  f n := ModuleCat.ofHom (DeRhamGlobal.PDDeRhamGlobal.formMap f hf n)
  comm' n m h := by
    change n + 1 = m at h
    subst m
    dsimp only [DeRham.PDDeRham.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun ω => (DeRhamGlobal.PDDeRhamGlobal.formMap_differential f hf n ω).symm)

theorem formMap_congr (f g : A ⟶ B) (h : f = g)
    (hf : DividedPowers.IsDPMorphism δ ε f.hom.toRingHom)
    (hg : DividedPowers.IsDPMorphism δ ε g.hom.toRingHom)
    (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δ n) :
    DeRhamGlobal.PDDeRhamGlobal.formMap f hf n ω = DeRhamGlobal.PDDeRhamGlobal.formMap g hg n ω := by
  subst g
  rfl

variable (e : A ≃ₐ[R] B)
  (he : DividedPowers.IsDPMorphism δ ε e.toRingHom)
  (hi : DividedPowers.IsDPMorphism ε δ e.symm.toRingHom)

theorem formMap_inverse (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δ n) :
    DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom e.symm.toAlgHom) hi n
      (DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom e.toAlgHom) he n ω) = ω := by
  have hcomp : (CommAlgCat.ofHom e.toAlgHom) ≫ (CommAlgCat.ofHom e.symm.toAlgHom) = 𝟙 A := by
    ext a
    exact e.symm_apply_apply a
  have hdp := hi.comp _ he
  have hc := DeRhamGlobal.PDDeRhamGlobal.formMap_comp (CommAlgCat.ofHom e.toAlgHom)
    (CommAlgCat.ofHom e.symm.toAlgHom) he hi hdp n ω
  exact hc.symm.trans ((formMap_congr _ _ hcomp hdp
    (DividedPowers.DPMorphism.id δ).isDPMorphism n ω).trans
      (DeRhamGlobal.PDDeRhamGlobal.formMap_id _ n ω))

def formsEquiv (n : ℕ) : DeRham.PDDeRham.Form R A I δ n ≃ₗ[R] DeRham.PDDeRham.Form R B J ε n :=
  LinearEquiv.ofLinearMap
    (DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom e.toAlgHom) he n)
    (DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom e.symm.toAlgHom) hi n)
    (LinearMap.ext (formMap_inverse e.symm hi he n))
    (LinearMap.ext (formMap_inverse e he hi n))

theorem formsEquiv_D (a : A) :
    formsEquiv e he hi 1 (OneForms.PDOneForms.D R A I δ a) = OneForms.PDOneForms.D R B J ε (e a) := by
  rw [OneForms.PDOneForms.D_apply, OneForms.PDOneForms.D_apply]
  change DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom e.toAlgHom) he 1
    (DeRham.PDDeRham.symbol R A I δ 1 (fun _ => a)) = _
  have hs := DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := A) (B := B)
    (CommAlgCat.ofHom e.toAlgHom) he 1 1 (fun _ => a)
  simp only [map_one] at hs
  exact hs

theorem formsEquiv_differential (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δ n) :
    formsEquiv e he hi (n + 1) (DeRham.PDDeRham.differential R A I δ n ω) =
      DeRham.PDDeRham.differential R B J ε n (formsEquiv e he hi n ω) :=
  DeRhamGlobal.PDDeRhamGlobal.formMap_differential (CommAlgCat.ofHom e.toAlgHom) he n ω

/-- Isomorphic PD algebras have isomorphic PD de Rham complexes. -/
def complexIso : DeRham.PDDeRham.complex R A I δ ≅ DeRham.PDDeRham.complex R B J ε where
  hom := complexMap (CommAlgCat.ofHom e.toAlgHom) he
  inv := complexMap (CommAlgCat.ofHom e.symm.toAlgHom) hi
  hom_inv_id := by
    ext n : 1
    apply ModuleCat.hom_ext
    exact LinearMap.ext (formMap_inverse e he hi n)
  inv_hom_id := by
    ext n : 1
    apply ModuleCat.hom_ext
    exact LinearMap.ext (formMap_inverse e.symm hi he n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence
