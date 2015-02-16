import java.util.*;

public class TestTimSort {
    private static final int MIN_MERGE = 32;
    private static final Comparator<Object> NATURAL_ORDER =
        new Comparator<Object>() {
            @SuppressWarnings("unchecked")
            public int compare(Object first, Object second) {
                return ((Comparable<Object>)first).compareTo(second);
            }
        };
    
    private final int minRun;
	private final List<Long> runs = new ArrayList<Long>();

    public static void main(String[] args) {
        int length = Integer.parseInt(args[0]);
        Arrays.sort(JDKWorstCase(length), NATURAL_ORDER);
    }
    
    private TestTimSort(int len) {
    	minRun = minRunLength(len);
    }

    private static int minRunLength(int n) {
        assert n >= 0;
        int r = 0;      // Becomes 1 if any 1 bits are shifted off
        while (n >= MIN_MERGE) {
            r |= (n & 1);
            n >>= 1;
        }
        return n + r;
    }
    
    /** 
     * Adds a sequence x_1, ..., x_n of run lengths to <code>runs</code> such that:<br>
     * 1. X = x_1 + ... + x_n <br>
     * 2. x_j >= minRun for all j <br>
     * 3. x_1 + ... + x_{j-2}  <  x_j  <  x_1 + ... + x_{j-1} for all j <br>
     * These conditions guarantee that TimSort merges all x_j's one by one
     * (resulting in X) using only merges on the second-to-last element.
     * @param X  The sum of the sequence that should be added to runs.
     */
    private void generateJDKWrongElem(long X) {
    	for(long newTotal; X >= 2*minRun+1; X = newTotal) {
    	    //Default strategy
    		newTotal = X/2 + 1;
    		
    		//Specialized strategies
    		if(3*minRun+3 <= X && X <= 4*minRun+1) {
    		    // add x_1=MIN+1, x_2=MIN, x_3=X-newTotal  to runs
    			newTotal = 2*minRun+1; 
    		} else if(5*minRun+5 <= X && X <= 6*minRun+5) {
    		    // add x_1=MIN+1, x_2=MIN, x_3=MIN+2, x_4=X-newTotal  to runs
    			newTotal = 3*minRun+3;
    		} else if(8*minRun+9 <= X && X <= 10*minRun+9) {
    		    // add x_1=MIN+1, x_2=MIN, x_3=MIN+2, x_4=2MIN+2, x_5=X-newTotal  to runs
    			newTotal = 5*minRun+5;
    		} else if(13*minRun+15 <= X && X <= 16*minRun+17) {
    		    // add x_1=MIN+1, x_2=MIN, x_3=MIN+2, x_4=2MIN+2, x_5=3MIN+4, x_6=X-newTotal  to runs
    			newTotal = 8*minRun+9;
    		}
    		runs.add(0, X-newTotal);
    	}
    	runs.add(0, X);
    }

    /** 
     * Fills <code>runs</code> with a sequence of run lengths of the form<br>
     * Y_n     x_{n,1}   x_{n,2}   ... x_{n,l_n} <br>
     * Y_{n-1} x_{n-1,1} x_{n-1,2} ... x_{n-1,l_{n-1}} <br>
     * ... <br>
     * Y_1     x_{1,1}   x_{1,2}   ... x_{1,l_1}<br>
     * The Y_i's are chosen to satisfy the invariant throughout execution,
     * but the x_{i,j}'s are merged (by <code>TimSort.mergeCollapse</code>)
     * into an X_i that violates the invariant. 
     * @param X  The sum of all run lengths that will be added to <code>runs</code>.
     */
    private void runsJDKWorstCase(int length) {
    	long runningTotal = 0, Y=minRun+4, X=minRun;
    	
    	while(runningTotal+Y+X <= length) {
            runningTotal += X + Y;
            generateJDKWrongElem(X);
    		runs.add(0,Y);
    		
    		// X_{i+1} = Y_i + x_{i,1} + 1, since runs.get(1) = x_{i,1} 
    		X = Y + runs.get(1) + 1;
    		
    		// Y_{i+1} = X_{i+1} + Y_i + 1
    		Y += X + 1;
    	}
    	
    	if(runningTotal + X <= length) {
            runningTotal += X;
            generateJDKWrongElem(X);
    	}
    	
    	runs.add(length-runningTotal);
    }

    private void runsCorrectWorstCase(int len) {
        long curr = minRun, prev=0;
        long runningTotal = len<minRun ? len : minRun;

        runs.add(runningTotal);
        
        while(runningTotal+prev+curr+1 <= len) {
            curr += prev+1;
            prev=curr-prev-1;
            runs.add(0, curr);
            runningTotal += curr;
        }
        
        runs.add(len-runningTotal);
    }

    private Integer[] createArray(int length) {
        Integer[] a = new Integer[length];
        Arrays.fill(a, 0);
        int endRun = -1;
        for(long len : runs)
            a[endRun+=len] = 1;
        a[length-1]=0;
        
        return a;
    }

    public static Integer[] JDKWorstCase(int length) {
        TestTimSort t = new TestTimSort(length);
        t.runsJDKWorstCase(length);
        return t.createArray(length);
    }

    public static Integer[] CorrectWorstCase(int length) {
        TestTimSort t = new TestTimSort(length);
        t.runsCorrectWorstCase(length);
        return t.createArray(length);
    }
}
