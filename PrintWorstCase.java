import java.util.Set;
import java.util.HashSet;

public class PrintWorstCase {
    private static final int MIN_MERGE = 32;
    private static final Set<Integer> WORST_CASE = new HashSet<Integer>();
    
    private static int minRun;

    public static void main(String[] args) {
        System.out.println(" Array size   Stack Size");
        for(int len=MIN_MERGE; len>0; len++) {
            int size = Math.max(JDKWorstCase(len), correctWorstCase(len));
            if(!WORST_CASE.contains(size)) {
                WORST_CASE.add(size);
                System.out.printf("%11d    %9d\n", len, size);
            }
        }
    }
    
    private static void setBound(long len) {
    	minRun = minRunLength(len);
    }

    private static int minRunLength(long n) {
        assert n >= 0;
        int r = 0;      // Becomes 1 if any 1 bits are shifted off
        while (n >= MIN_MERGE) {
            r |= (n & 1);
            n >>= 1;
        }
        return (int)n + r;
    }
    
    private static long first(long total) {
    	if(    (8*minRun+9 <= total)
    		|| (5*minRun+5 <= total && total <= 8*minRun+1)
    		|| (3*minRun+3 <= total && total <= 4*minRun+1)) {
    		return minRun+1;
    	}
    	while(total >= 2*minRun+1)
    		total=total/2+1;
    	return total;
    }
    
    public static int JDKWorstCase(long length) {
        setBound(length);
        int stackSize=0;
    	long runningTotal=0, curr=minRun+4, prev=minRun;
    	
    	while(runningTotal+curr+prev <= length) {
            runningTotal += prev + curr;
            stackSize +=2;
            long diff = first(prev);
    		prev = curr + diff + 1;
    		curr += prev + 1;
    	}
    	
    	if(runningTotal + prev <= length) {
            runningTotal += prev;
            stackSize++;
    	}
    	
    	if(runningTotal < length)
    	    stackSize++;
    	return stackSize;
    }

    public static int correctWorstCase(int length) {
        setBound(length);
        int stackSize=1;
        long curr = minRun, prev=0;
        long runningTotal = length<minRun ? length : minRun;
        
        while(runningTotal+prev+curr+1 <= length) {
            curr += prev+1;
            prev=curr-prev-1;
            runningTotal += curr;
            stackSize++;
        }
        
        if(runningTotal < length)
            stackSize++;
        return stackSize;
    }
}
