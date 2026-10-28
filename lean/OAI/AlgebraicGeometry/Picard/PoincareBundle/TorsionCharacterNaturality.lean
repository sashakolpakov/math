import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionCharacterPoint
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues

/-! # Torsion Character Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionCharacterNaturality

noncomputable section

/-! The actual torsion character and its regular-unit value are natural on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

/-- The actual torsion lift respects every test-scheme restriction. -/
theorem lift_natural {S : Scheme.{u}} (A : Over S) [GrpObj A] (n : ℕ) {T U : Over S} (a : U ⟶ T)
    (x : T ⟶ A) (hx : x ^ n = 1) (hxa : (a ≫ x) ^ n = 1) :
    a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n x hx = AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (a ≫ x) hxa := by
  have : Mono (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 A) ^ n) 1))
  apply (cancel_mono (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).mp
  rw [Category.assoc, AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι, AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι]

/-- A group homomorphism maps n-torsion into n-torsion. -/
theorem image_torsion {S : Scheme.{u}} {X Z : Over S} [GrpObj X] [GrpObj Z]
    (ell : X ⟶ Z) [IsMonHom ell] (n : ℕ) {T : Over S} (x : T ⟶ X) (hx : x ^ n = 1) :
    (x ≫ ell) ^ n = 1 := by
  simpa only [MonObj.pow_comp, MonObj.one_comp] using congrArg (fun z => z ≫ ell) hx

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A) ^ n).left] [Flat ((𝟙 A) ^ n).left]
  [Surjective ((𝟙 A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A) ^ n).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))

/-- Restriction preserves the actual inverse Cartier character. -/
theorem character_natural {T U : Over (Spec (.of k))} (a : U ⟶ T)
    (p : T ⟶ D.abelian) (hp : p ^ n = 1) (hpa : (a ≫ p) ^ n = 1) :
    (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.map a.op
        (TorsionCharacterPoint.character A D ell n hn C p hp) =
      TorsionCharacterPoint.character A D ell n hn C (a ≫ p) hpa := by
  apply TorsionCharacterPoint.unique A D ell n hn C
  exact (AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterDualPoint_natural ((𝟙 A) ^ n) a
    (TorsionCharacterPoint.character A D ell n hn C p hp) D).symm.trans
      (congrArg (fun q => a ≫ q) (TorsionCharacterPoint.point A D ell n hn C p hp))

/-- The regular unit obtained by evaluating the actual Cartier character. -/
def value {T : Over (Spec (.of k))} (p : T ⟶ D.abelian) (hp : p ^ n = 1)
    (x : T ⟶ A) (hx : x ^ n = 1) : Γ(T.left, ⊤)ˣ :=
  AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value
    (TorsionCharacterPoint.character A D ell n hn C p hp) (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n x hx))

/-- No reduction of the parameter scheme is used in the naturality of the Weil unit. -/
theorem value_natural {T U : Over (Spec (.of k))} (a : U ⟶ T)
    (p : T ⟶ D.abelian) (hp : p ^ n = 1) (hpa : (a ≫ p) ^ n = 1)
    (x : T ⟶ A) (hx : x ^ n = 1) (hxa : (a ≫ x) ^ n = 1) :
    value A D ell n hn C (a ≫ p) hpa (a ≫ x) hxa =
      Units.map a.left.appTop.hom (value A D ell n hn C p hp x hx) := by
  let χ := TorsionCharacterPoint.character A D ell n hn C p hp
  let z : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n) := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n x hx
  have hc := character_natural A D ell n hn C a p hp hpa
  have hz := lift_natural A n a x hx hxa
  have he : AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value
      (TorsionCharacterPoint.character A D ell n hn C (a ≫ p) hpa)
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (a ≫ x) hxa) = a ≫ AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ z :=
    (congrArg₂ (fun (ψ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))).obj.obj (.op U))
      (v : U ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) => AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value ψ v) hc.symm hz.symm).trans
      (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_natural (F := yonedaGrp.obj (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
        (K := yonedaGrp.obj (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k)))) a χ z)
  exact (congrArg (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U) he).trans
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom_natural a (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ z)).symm

/-- Restrict the standard Weil evaluation by the supplied homomorphism in its dual variable. -/
def source_value {T : Over (Spec (.of k))} (x : T ⟶ A) (hx : x ^ n = 1)
    (y : T ⟶ A) (hy : y ^ n = 1) : Γ(T.left, ⊤)ˣ :=
  value A D ell n hn C (x ≫ ell) (image_torsion ell n x hx) y hy

/-- The restricted pairing is natural on the full n-torsion functor. -/
theorem source_value_natural {T U : Over (Spec (.of k))} (f : U ⟶ T)
    (x : T ⟶ A) (hx : x ^ n = 1) (hxf : (f ≫ x) ^ n = 1)
    (y : T ⟶ A) (hy : y ^ n = 1) (hyf : (f ≫ y) ^ n = 1) :
    source_value A D ell n hn C (f ≫ x) hxf (f ≫ y) hyf =
      Units.map f.left.appTop.hom (source_value A D ell n hn C x hx y hy) := by
  have hxp := image_torsion ell n x hx
  have hxpf : (f ≫ (x ≫ ell)) ^ n = 1 := by
    simpa only [Category.assoc] using image_torsion ell n (f ≫ x) hxf
  let p0 : {q : U ⟶ D.abelian // q ^ n = 1} :=
    ⟨(f ≫ x) ≫ ell, image_torsion ell n (f ≫ x) hxf⟩
  let p1 : {q : U ⟶ D.abelian // q ^ n = 1} := ⟨f ≫ (x ≫ ell), hxpf⟩
  have hsub : p0 = p1 := Subtype.ext (Category.assoc f x ell)
  have he := congrArg (fun p : {q : U ⟶ D.abelian // q ^ n = 1} =>
    value A D ell n hn C p.val p.property (f ≫ y) hyf) hsub
  exact he.trans (value_natural A D ell n hn C f (x ≫ ell) hxp hxpf y hy hyf)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionCharacterNaturality
