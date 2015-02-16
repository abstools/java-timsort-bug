/* This file has been generated by Stubmaker (de.uka.ilkd.stubmaker)
 * Date: Wed Nov 26 11:26:00 CET 2014
 */
package java.nio;

public abstract class FloatBuffer extends java.nio.Buffer implements java.lang.Comparable
{
   final float[] hb;
   final int offset;
   boolean isReadOnly;


   /*@ requires true; ensures true; assignable \everything; */
   public static java.nio.FloatBuffer allocate(int arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public static java.nio.FloatBuffer wrap(float[] arg0, int arg1, int arg2);

   /*@ requires true; ensures true; assignable \everything; */
   public static java.nio.FloatBuffer wrap(float[] arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.FloatBuffer slice();

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.FloatBuffer duplicate();

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.FloatBuffer asReadOnlyBuffer();

   /*@ requires true; ensures true; assignable \everything; */
   public abstract float get();

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.FloatBuffer put(float arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public abstract float get(int arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.FloatBuffer put(int arg0, float arg1);

   /*@ requires true; ensures true; assignable \everything; */
   public java.nio.FloatBuffer get(float[] arg0, int arg1, int arg2);

   /*@ requires true; ensures true; assignable \everything; */
   public java.nio.FloatBuffer get(float[] arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public java.nio.FloatBuffer put(java.nio.FloatBuffer arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public java.nio.FloatBuffer put(float[] arg0, int arg1, int arg2);

   /*@ requires true; ensures true; assignable \everything; */
   public final java.nio.FloatBuffer put(float[] arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public final boolean hasArray();

   /*@ requires true; ensures true; assignable \everything; */
   public final float[] array();

   /*@ requires true; ensures true; assignable \everything; */
   public final int arrayOffset();

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.FloatBuffer compact();

   /*@ requires true; ensures true; assignable \everything; */
   public abstract boolean isDirect();

   /*@ requires true; ensures true; assignable \everything; */
   public java.lang.String toString();

   /*@ requires true; ensures true; assignable \everything; */
   public int hashCode();

   /*@ requires true; ensures true; assignable \everything; */
   public boolean equals(java.lang.Object arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public int compareTo(java.nio.FloatBuffer arg0);

   /*@ requires true; ensures true; assignable \everything; */
   public abstract java.nio.ByteOrder order();

   /*@ requires true; ensures true; assignable \everything; */
   public java.lang.Object array();

   /*@ requires true; ensures true; assignable \everything; */
   public int compareTo(java.lang.Object arg0);
}