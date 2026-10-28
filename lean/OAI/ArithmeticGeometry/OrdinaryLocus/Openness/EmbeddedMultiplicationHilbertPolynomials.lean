import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleUnitSectionDimension
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationHilbertPolynomials
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupProjectiveHilbertDegree
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbertNonzero

/-! # Embedded Multiplication Hilbert Polynomials -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedMultiplicationHilbertPolynomials.Construction

noncomputable section

/-! The chosen ample embedding supplies nonzero Hilbert polynomials with the multiplication rescaling and geometric degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

local instance embeddedMultiplicationHilbertPolynomialsMonoidal (X : Scheme.{0}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem embedded_multiplication_Hilbert_polynomials
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple)
    (hs : Nonempty ((L.pullback ((𝟙 A : A ⟶ A)⁻¹).left).sheaf ≅ L.sheaf))
    (m : ℕ) (hm : 0 < m) [IsFinite (Multiplication.Construction.multiplicationMap A m).left]
    (d r : ℕ) (hd : 0 < d)
    (a : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(Spec (.of K), ⊤)))
    [IsClosedImmersion a]
    (hb : a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = A.hom ≫ (Spec (.of K)).toSpecΓ)
    (e : (Scheme.Modules.pullback a).obj
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(Spec (.of K), ⊤)) (0 : Fin (r + 1))).sheaf ≅
      (L.tensorPower d).sheaf) :
    ∃ (P Q : Polynomial ℚ) (b : ℕ), P ≠ 0 ∧
      (P.natDegree : WithBot ℕ∞) = topologicalKrullDim A.left ∧
      (∀ n, b ≤ n →
        (Module.finrank Γ(Spec (.of Γ(Spec (.of K), ⊤)), ⊤)
          ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
            ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower 0 n))) : ℚ) =
          P.eval (n : ℚ)) ∧
      (∀ n, b ≤ n →
        (Module.finrank Γ(Spec (.of Γ(Spec (.of K), ⊤)), ⊤)
          ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
            ((Scheme.Modules.pushforward (Multiplication.Construction.multiplicationMap A m).left).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.left) ⊗
              (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower 0 n))) : ℚ) =
          Q.eval (n : ℚ)) ∧
      Q = P.comp (Polynomial.X * Polynomial.C ((m ^ 2 : ℕ) : ℚ)) := by
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  let R := Γ(Spec (.of K), ⊤)
  let : Field R := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  let : Field Γ(Spec (.of R), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField R
  let O := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.left
  have : O.IsQuasicoherent := LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (LineBundle.Construction.isLineBundle_structureSheaf A.left)
  have : O.IsFiniteType := ProjectiveCohomologyFiniteness.Construction.isFiniteType_of_isLineBundle _ (LineBundle.Construction.isLineBundle_structureSheaf A.left)
  let F := (Scheme.Modules.pushforward (Multiplication.Construction.multiplicationMap A m).left).obj O
  have : F.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _
  have : F.IsFiniteType := FinitePushforward.Construction.finitePushforward_isFiniteType _ O
  obtain ⟨P, _, bP, hp⟩ := ClosedProjectiveHilbert.Construction.closedProjective_sections_eventuallyPolynomial a O 0 (Field.toIsField _)
  obtain ⟨Q, _, bQ, hq⟩ := ClosedProjectiveHilbert.Construction.closedProjective_sections_eventuallyPolynomial a F 0 (Field.toIsField _)
  let b := max bP bQ
  have hP (n : ℕ) (hn : b ≤ n) :
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower 0 n))) : ℚ) =
      P.eval (n : ℚ) := by
    have he := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
      (ProjectivePolynomialQuotient.Construction.structureModuleTensorLeftIso ((Scheme.Modules.pullback a).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) 0 n)))).toLinearEquiv.finrank_eq
    exact (congrArg (fun k : ℕ => (k : ℚ)) he).symm.trans (hp n ((le_max_left _ _).trans hn))
  have hQ (n : ℕ) (hn : b ≤ n) := hq n ((le_max_right bP bQ).trans hn)
  have hPL (n : ℕ) (hn : b ≤ n) :
      (Module.finrank R ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj (L.tensorPower (n * d)).sheaf) : ℚ) =
      P.eval (n : ℚ) :=
    (congrArg (fun k : ℕ => (k : ℚ)) (AmpleUnitSectionDimension.Construction.embeddedAmpleSection_finrank A.hom L d r a hb e n)).symm.trans
      (hP n hn)
  have hQL (n : ℕ) (hn : b ≤ n) :
      (Module.finrank R ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj
        (SheafTensor.Construction.sheafTensor F (L.tensorPower (n * d)).sheaf)) : ℚ) = Q.eval (n : ℚ) :=
    (congrArg (fun k : ℕ => (k : ℚ)) (EmbeddedAmpleSectionDimension.Construction.embeddedAmpleTwistSection_finrank A.hom L d r a hb e F n)).symm.trans
      (hQ n hn)
  refine ⟨P, Q, b, AmpleHilbertNonzero.Construction.ampleHilbertPolynomial_ne_zero A.hom (Field.toIsField _) L hL d hd P b hPL,
    GroupProjectiveHilbertDegree.Construction.group_projective_Hilbert_natDegree A (Field.toIsField _) a 0 P b hP, hP, hQ, ?_⟩
  apply EventualPolynomialIdentity.Construction.polynomial_comp_mul_of_eventually_eval P Q (m ^ 2) b
  intro n hn
  have hnm : n ≤ n * m ^ 2 := Nat.le_mul_of_pos_right n (pow_pos hm 2)
  have he := congrArg (fun k : ℕ => (k : ℚ))
    (MultiplicationHilbertSections.Construction.multiplication_pushforward_sections_finrank A L hs m (n * d))
  have hexp : (n * d) * m ^ 2 = (n * m ^ 2) * d := by ac_rfl
  rw [hexp] at he
  exact (hQL n hn).symm.trans (he.trans (hPL (n * m ^ 2) (hn.trans hnm)))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedMultiplicationHilbertPolynomials.Construction
