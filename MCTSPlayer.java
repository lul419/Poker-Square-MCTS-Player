import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Random;
import java.util.Scanner;
import java.util.Stack;
import java.util.List;
import java.util.LinkedList;
import java.util.Objects;

public class MCTSPlayer implements PokerSquaresPlayer {
    private final double epsilon = 1e-6;
    private final int SIZE = 5; // number of rows/columns in square grid
    private final int NUM_POS = SIZE * SIZE; // number of positions in square grid
    private final int NUM_CARDS = Card.NUM_CARDS; // number of cards in deck
    private Random random = new Random();
    private int[] plays = new int[NUM_POS]; // positions of plays so far (index 0 through numPlays - 1) recorded as integers using row-major indices.
    // row-major indices: play (r, c) is recorded as a single integer r * SIZE + c (See http://en.wikipedia.org/wiki/Row-major_order)
    // From plays index [numPlays] onward, we maintain a list of yet unplayed positions.
    private int numPlays = 0; // number of Cards played into the grid so far
    private int numTrialsPerDeck = 10;
    private int numSimulationsPerRollout = 1;
    private double selectionConstant = 10;
    public PokerSquaresPointSystem system;
    private Card[][] grid = new Card[SIZE][SIZE]; // grid with Card objects or null (for empty positions) Card[row][col]
    private Card[] deck = Card.getAllCards();
    private List<Card> list = Arrays.asList(deck);
    private LinkedList<Card> simDeck = new LinkedList<Card>();
    
    public MCTSPlayer() {
    }

    // constructor to manually set numTrials, numSimulations, selectionConstant
    public MCTSPlayer(int ntpd, int nspr, double sc) {
        numTrialsPerDeck = ntpd;
        numSimulationsPerRollout = nspr;
        selectionConstant = sc;
    }

    
    public int[] getPlay(Card card, long millisRemaining) {
        
        // (This avoids constant allocation/deallocation of such lists during the greedy selections of MC simulations.)
        LinkedList<Card> temporarySimDeck = new LinkedList<Card>();
        int[] playToReturn = new int[2];
        int remainingPlays = NUM_POS - numPlays; // ignores triviality of last play to keep a conservative margin for game completion
        long millisPerPlay = (millisRemaining - 1000) / remainingPlays; // dividing time evenly with future getPlay() calls
        long startTime = System.currentTimeMillis();
        long endTime = startTime + millisPerPlay;
        //System.out.println("num "+numPlays);
        
        if (numPlays ==0) {
            simDeck.addAll(list);
            simDeck.remove(card);
            grid[0][0]=card;
            playToReturn[0]=0;
            playToReturn[1]=0;
        }

        else if (numPlays<24){ 
            simDeck.remove(card);
            PlayNode parent = new PlayNode(numPlays, grid);
            
            while (System.currentTimeMillis()  < endTime) {
                
                // create new shuffled sim deck to use
                temporarySimDeck = (LinkedList<Card>) simDeck.clone();
                Collections.shuffle(temporarySimDeck, random);
                temporarySimDeck.push(card);
                
                // create trial
                for(int x = 0;x<numTrialsPerDeck;x++) {
                    parent.selectAction(temporarySimDeck);
                }
                
                //reset nodes
                for(PlayNode node: parent.children) {
                    node.children = null;
                }
                temporarySimDeck.clear();
            }
            
            double bestScore = Double.MIN_VALUE;
            PlayNode bestNode = parent.select();
            
            for(int a = 0; a<SIZE; a++) {
                for (int b = 0; b<SIZE; b++) {
                    if (bestNode.board[a][b] == card) {
                        playToReturn[0] = a;
                        playToReturn[1] = b;
                        grid[a][b] = card;
                    }
                }
            }            
        }
        else{
            for(int i = 0; i < NUM_POS; i++) {
                if (grid[i/SIZE][i % SIZE] == null) {
                    playToReturn[0]=i/SIZE;
                    playToReturn[1]=i%SIZE;
                    grid[i/SIZE][i % SIZE]=card;
                }
            }
        }
        numPlays++;

        return playToReturn;
    }
    
    public void setPointSystem(PokerSquaresPointSystem system, long millis){
        this.system = system;
    }
    
    public void init() {
        
        // clear grid
        for (int row = 0; row < SIZE; row++)
            for (int col = 0; col < SIZE; col++)
                grid[row][col] = null;
            
        // reset numPlays
        numPlays = 0;
        
        // (re)initialize list of play positions (row-major ordering)
        for (int i = 0; i < NUM_POS; i++)
            plays[i] = i;
    }
    
    public String getName() {
        return "MCTS Player (Isaac, Lucy, Meg)";
    }
    
    private class PlayNode {
        
        private Card[][] board;
        private int nActions; // number of actions made so far in this simulation
        private PlayNode[] children;
        private PlayNode parent;
        private double nVisits = 0;
        private double totValue = 0;
        
        private PlayNode(PlayNode parent, Card[][] board){ //for tree branches, called by nodes
            this.board = board;
            this.parent = parent;
            this.nActions=parent.nActions+1;
            
        }
        
        public PlayNode(int numPlays, Card[][] board){ //For tree root, called by MCTS player
            this.board= board;
            this.parent=null;
            nActions=numPlays;
        }
        
        public void selectAction(LinkedList<Card> temporaryDeck) {
            
            LinkedList<Card> deckForSelectAction = (LinkedList<Card>) temporaryDeck.clone();
                        
            List<PlayNode> visited = new LinkedList<PlayNode>();
            PlayNode cur = this;
            
            // tree policy
            visited.add(this);
            while (!cur.isLeaf()) {
                cur = cur.select();
                deckForSelectAction.pop();
                visited.add(cur);
            }

            // expand
            Card cardToPlay = deckForSelectAction.pop();
            cur.expand(cardToPlay);
            
            // select
            PlayNode newNode;
            if (cur.nActions == NUM_POS) {
                newNode = cur;
            }
            else {
                newNode = cur.select();
                visited.add(newNode);
            }
            
            // roll out and update stats for each node
            double value = 0;
            for(int i = 0; i<numSimulationsPerRollout; i++) {
                value = value + newNode.rollOut(deckForSelectAction);
            }
            for (PlayNode node : visited) {
                
                node.updateStats(value);
            }
        }
        
        public void expand(Card cardToPlay) {
            
            if (nActions ==NUM_POS) {
                children = null;
                return;
            }
            
            else {                
                PlayNode[] children = new PlayNode[NUM_POS-nActions];
                int cardPos=0;
                
                for (int i=0; i<NUM_POS-nActions; i++) {
                    Card[][] currentBoard = new Card[SIZE][SIZE];
                    for(int j = 0; j < NUM_POS; j++) {
                        currentBoard[j/SIZE][j%SIZE] = board[j/SIZE][j%SIZE];
                    }//JANKY CODE                    
                    
                    while (this.board[cardPos / SIZE][cardPos % SIZE] != null){
                        cardPos++;
                        
                    }
                    
                    currentBoard[cardPos / SIZE][cardPos % SIZE] = cardToPlay;
                    children[i] = new PlayNode(this, currentBoard);
                    cardPos++;                    
                }
                this.children = children;
            }
        }
        
        private PlayNode select() {
            PlayNode selected = null;
            double bestValue = Double.MIN_VALUE;
            
            // go through each child and select best
            for (PlayNode c : children) {    
                double uctValue = c.totValue / (c.nVisits + epsilon) +
                selectionConstant *(Math.sqrt(Math.log(nVisits+1) / (c.nVisits + epsilon))) +
                random.nextDouble() * epsilon;
                // small random number to break ties randomly in unexpanded nodes
                if (uctValue > bestValue) {
                    selected = c;
                    bestValue = uctValue;
                }
            }
            return selected;
        }
        
        public boolean isLeaf() {
            return children == null;
        }
        
        public double rollOut(LinkedList<Card> temporaryDeck) {

            LinkedList<Card> deckForRollout = (LinkedList<Card>) temporaryDeck.clone();
            
            // copy current board to new board to fill for rollout
            Card[][] boardToFill = new Card[SIZE][SIZE];
            for(int j = 0; j < NUM_POS; j++) {
                boardToFill[j/SIZE][j%SIZE] = board[j/SIZE][j%SIZE];
            }//JANKY CODE
            Stack<Integer> emptyPositions = new Stack<Integer>();
            
            // find all empty positions of board
            for(int i = 0; i < NUM_POS; i++) {
                if (boardToFill[i/SIZE][i % SIZE] == null) {
                    emptyPositions.push(new Integer(i));
                }
                
            }
            
            // get an empty position randomly to put next card in
            Collections.shuffle(emptyPositions, random);
            while(!emptyPositions.empty()) {
                
                int square = emptyPositions.pop().intValue();
                boardToFill[square / SIZE][square %SIZE] = deckForRollout.pop();
            }
            double finalscore = system.getScore(boardToFill);
            return finalscore;
            
        }
        
        public void updateStats(double value) {
            nVisits++;
            totValue += value;
        }
        
        public int arity() {
            return children == null ? 0 : children.length;
        }
    }

    public static void main(String[] args) {
        PokerSquaresPointSystem system = PokerSquaresPointSystem.getAmericanPointSystem();
        System.out.println(system);
        int score = 0;
        for (int i=0;i<1;i++){
            int value=new PokerSquares(new MCTSPlayer(), system).play(); // play a single game
            score=score+value;

        }
        //System.out.println("score"+score/10);
    }
}