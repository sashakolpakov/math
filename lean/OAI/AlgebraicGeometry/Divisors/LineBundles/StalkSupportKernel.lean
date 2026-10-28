import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap

/-! # Stalk Support Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkSupportKernel.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual support stalk is the quotient by the corresponding local prime

The support's actual stalk map is surjective. Its kernel prime maps to
the support's generic point, so injectivity of the ambient stalk-spectrum
map identifies that kernel with the corresponding local prime.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))

def supportLocalPoint : CycleClass.Geometric.GenericPoint.reducedSupportScheme W :=
  Classical.choose ((congrArg (fun S : Set X => x ∈ S) (CycleClass.Geometric.GenericPoint.range_reducedSupportι W)).mpr hx)

theorem supportLocalPoint_spec : CycleClass.Geometric.GenericPoint.reducedSupportι W (supportLocalPoint X W x hx) = x :=
  Classical.choose_spec ((congrArg (fun S : Set X => x ∈ S) (CycleClass.Geometric.GenericPoint.range_reducedSupportι W)).mpr hx)

def supportLocalStalkMap :
    X.presheaf.stalk x ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (supportLocalPoint X W x hx) :=
  eqToHom (congrArg (fun y => X.presheaf.stalk y) (supportLocalPoint_spec X W x hx).symm) ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (supportLocalPoint X W x hx)

theorem supportLocalStalkMap_surjective : Function.Surjective (supportLocalStalkMap X W x hx) :=
  ((CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap_surjective _).comp
    (ConcreteCategory.bijective_of_isIso (eqToHom
      (congrArg (fun y => X.presheaf.stalk y) (supportLocalPoint_spec X W x hx).symm))).surjective

omit W x hx in
theorem stalkMap_point_square {A : Scheme} (i : A ⟶ X) (a : A) (x : X) (h : i a = x) :
    Spec.map (eqToHom (congrArg (fun y => X.presheaf.stalk y) h.symm) ≫ i.stalkMap a) ≫
      X.fromSpecStalk x = A.fromSpecStalk a ≫ i := by
  subst x
  simp only [eqToHom_refl, Category.id_comp]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk i

def supportLocalKernelPrime : Spec (X.presheaf.stalk x) :=
  ⟨RingHom.ker (supportLocalStalkMap X W x hx).hom,
    Ideal.isPrime_bot.comap (supportLocalStalkMap X W x hx).hom⟩

theorem supportLocalKernelPrime_image :
    X.fromSpecStalk x (supportLocalKernelPrime X W x hx) = irreducibleSetEquivPoints W := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let a := supportLocalPoint X W x hx
  let T := A.presheaf.stalk a
  have he := congrArg (fun j : Spec T ⟶ X => j (genericPoint (Spec T)))
    (stalkMap_point_square X (CycleClass.Geometric.GenericPoint.reducedSupportι W) a x (supportLocalPoint_spec X W x hx))
  change X.fromSpecStalk x ((Spec.map (supportLocalStalkMap X W x hx)) (genericPoint (Spec T))) =
    CycleClass.Geometric.GenericPoint.reducedSupportι W (A.fromSpecStalk a (genericPoint (Spec T))) at he
  rw [StalkLocalization.BundleCycles.fromSpecStalk_genericPoint, CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq, genericPoint_eq_bot_of_affine] at he
  exact he

theorem supportLocalStalkMap_kernel (p : Spec (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = irreducibleSetEquivPoints W) :
    RingHom.ker (supportLocalStalkMap X W x hx).hom = p.asIdeal := by
  have he : supportLocalKernelPrime X W x hx = p :=
    (X.fromSpecStalk x).isEmbedding.injective ((supportLocalKernelPrime_image X W x hx).trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkSupportKernel.BundleCycles
