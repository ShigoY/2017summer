package convertor;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Stream;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.parameters.Imports;

public class AuxiliaryAxioms {
	private static Convertor convertor;
	private static Set<String> inversed=new HashSet<String>();
	
	public static void toSet(String str){
		inversed.add(str);
	}
	
	public static void set_convertor(Convertor conv){
		convertor=conv;
	}
	
	public static String fixedDomainInClass(OWLClass c){
		StringBuffer s=new StringBuffer();
		String cname=convertor.getComponentsID(c);
		s.append("![X]:(("+cname+"(X)=>iThing(X))&(~"+cname+"(X)=>iThing(X)))");
		return s.toString();
	}
	
	public static String fixedDomainInObjectProperty(OWLObjectProperty r){
		StringBuffer s=new StringBuffer();
		String rname=convertor.getComponentsID(r);
		s.append("![X,Y]:(("+rname+"(X,Y)=>(iThing(X)&iThing(Y)))&(~"+rname+"(X,Y)=>(iThing(X)&iThing(Y))))");
		return s.toString();
	}
	
	public static void addFixedDomainInClasses(OWLOntology ontology){
		Stream<OWLClass> sc=ontology.classesInSignature(Imports.INCLUDED);
		sc.forEach(p->System.out.println(convertor.addHeader(fixedDomainInClass(p),"axiom")));
	}
	
	public static void addFixedDomainInProperties(OWLOntology ontology){
		Stream<OWLObjectProperty> sr=ontology.objectPropertiesInSignature(Imports.INCLUDED);
		sr.forEach(p->System.out.println(convertor.addHeader(fixedDomainInObjectProperty(p),"axiom")));
	}
	
	public static void addFixedDomainAxiom(OWLOntology ontology){
		try{
			Stream<OWLNamedIndividual> inds=ontology.individualsInSignature(Imports.INCLUDED);
			StringBuffer s=new StringBuffer();
			s.append("![X]:(");
			//s.append("iThing(X)=>(");
			inds.forEach(p->s.append("X="+convertor.getComponentsID((OWLIndividual)p)+"|"));
			s.deleteCharAt(s.length()-1);
			s.append(")");
			if(s.equals("")==false) {
				System.out.println(convertor.addHeader(s.toString(),"fi"));
			}
		}catch(NullPointerException e){
			System.out.println("no domain element specified.");
			e.printStackTrace();
		}
	}
	
	public static String inverseRoles(String str){
		StringBuffer s=new StringBuffer();
		s.append("![X,Y]:(inv_"+str+"(X,Y)<=>"+str+"(Y,X))");
		return s.toString();
	}
	
	public static void addInverseRoles(){
		for(Iterator<String> it=inversed.iterator();it.hasNext();){
			System.out.println(convertor.addHeader(inverseRoles(it.next()),"axiom"));
		}
	}
	
}
