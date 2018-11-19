package analysis;

import java.util.HashSet;
import java.util.Set;

import soot.Value;

/**
 * The Class FileStateFact records the state of a file object
 */
public class FileStateFact{
	
	/** The aliases point to the same File object. */
	private Set<Value> aliases;
	/** The state of the file object.*/
	private FileState state;

	public FileStateFact(Set<Value> aliases, FileState state) {
		if (aliases != null)
			this.aliases = aliases;
		else
			this.aliases = new HashSet<Value>();
		this.state = state;
	}

	public void updateState(FileState state) {
		this.state = state;
	}

	public void addAlias(Value alias) {
		this.aliases.add(alias);
	}

	public boolean isOpened() {
		return state.equals(FileState.Open);
	}

	public boolean containsAlias(Value value) {
		for (Value alias : aliases) {
			if (alias.toString().equals(value.toString()))
				return true;
		}
		return false;
	}

	public boolean containsAlias(String value) {
		for (Value alias : aliases) {
			if (alias.toString().equals(value))
				return true;
		}
		return false;
	}

	public FileState getState() {
		return this.state;
	}

	@Override
	public String toString() {
		return "(" + aliases + ", " + state + ")";
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((aliases == null) ? 0 : aliases.hashCode());
		result = prime * result + ((state == null) ? 0 : state.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FileStateFact other = (FileStateFact) obj;
		if (aliases == null) {
			if (other.aliases != null)
				return false;
		} else if (!aliases.equals(other.aliases))
			return false;
		if (state != other.state)
			return false;
		return true;
	}

	public FileStateFact copy()
	{
		return new FileStateFact(aliases, state);
	}

}
