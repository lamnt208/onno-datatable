# onno-datatable
=======
# onno-datatable

> Made with create-react-library

[![NPM](https://img.shields.io/npm/v/onno-datatable.svg)](https://www.npmjs.com/package/onno-datatable) [![JavaScript Style Guide](https://img.shields.io/badge/code_style-standard-brightgreen.svg)](https://standardjs.com)

## Install

```bash
npm install --save onno-datatable
or
npm install --save-dev onno-datatable
```

## Usage

```jsx
import React, { Component } from 'react';

import Table, { Column } from 'onno-datatable';
import 'onno-datatable/dist/index.css';

class Example extends Component {
  	render() {
		return <Table
			data={teams}
			filterable={true}
			tableClassNames={['table', 'table-bordered', 'table-striped', 'table-hover', 'table-sm']}
			headerClassNames={['thead-dark']}
		>
			<Column label="Name" field="name" sortable={true} />
			<Column label="Status" field="enable" sortable={true} render={(each) => each.enable === 'Yes' ?
				(<Badge variant="success">Enabled</Badge>) :
				(<Badge variant="danger">Disabled</Badge>)} />
			<Column label="Action" hidden={!userInfo.isAdmin} render={(each) => (
				<>
					<a href="javascript:void(0)" className="mr-2 small" onClick={this.onChangeStatus(each)}>
						{each.enable === 'Yes' ?
							(<span className="text-danger"><i className="fas fa-trash-alt"></i> Disabled </span>) :
							(<span className="text-success"><i className="fas fa-eye"></i> Enable </span>)}
					</a>
					<a className="text-secondary small" onClick={this.onOpenEditForm(each)} href="javascript:void(0)">
						<i className="fas fa-edit"></i> Edit
								</a>
				</>
			)} />
		</Table>;
  	}
}
```

## User guide

**Table**

| Prop name  | Description | Default value | Example values
| ------------- | ------------- | ------------- | ------------- |
| children (required)  | Includes many Columns | n/a | <Column /> |
| data  | array objects  | [] | [{ "Name": "Tiger Nixon", "Position": "System Architect" }] |
| width  | width of table | '100%' | '90px' |
| pageSizes  | Total pageSize value which are displayed on page size combobox | [5, 10, 25, 50, 75, 100] | [7, 10, 40] |
| filterable  | Allow search on table | true |  |
| sortAscIcon  | Icon Sort Asc, display on header | n/a |  |
| sortDescIcon  | Icon Sort Desc, display on header | n/a |  |
| sortIcon  | Icon Sort, display on header | n/a | |
| tableClassNames  | Classnames of table | ['table', 'table-bordered'] | |
| headerClassNames  | Classnames of header | [] | |

**Column**

| Prop name  | Description | Default value | Example values
| ------------- | ------------- | ------------- | ------------- |
| label  | Label of column, display on header | n/a | 'Name', 'Age' |
| field  | field value | n/a | 'name |
| sortable  | Allow to sort of column | false |  |
| hidden  | Show or hide a column | false |  |
| render  | Custom render cell | n/a | <b>{record.name}</b> |
| sortingBy  | Default sort when render the first time | n/a | 'ASC' |


## License

MIT © [lamnt.it@gmail.com](https://github.com/lamnt208)
